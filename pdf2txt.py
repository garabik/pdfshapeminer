#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import print_function

import sys
from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter
import random, copy
from math import atan2, pi

from pprint import pprint

from pdfminer.pdfdocument import PDFDocument
from pdfminer.pdfparser import PDFParser
from pdfminer.pdfinterp import PDFResourceManager, PDFPageInterpreter
from pdfminer.pdfdevice import PDFDevice, TagExtractor
from pdfminer.pdfpage import PDFPage
from pdfminer.converter import XMLConverter, HTMLConverter, TextConverter
from pdfminer.cmapdb import CMapDB
from pdfminer.layout import LAParams
from pdfminer.image import ImageWriter

from pdfminer.utils import bbox2str

from pdfminer.layout import LTContainer, LTText, LTTextBox, LTImage, LTTextLine, LTChar, LTTextLineHorizontal

import shapely.geometry
from matplotlib import pyplot

debuglevel = 0
def DEBUG(level, *msg, **args):
    end = args.get('end', '\n')
    if level<=debuglevel:
        print(*msg, file=sys.stderr, end=end)
        sys.stderr.flush()

def msg(*s):
    r = ' '.join(str(x) for x in s)
    sys.stderr.write(r); sys.stderr.flush()

def msgn(*s):
    msg(*s)
    msg('\n')

def msgr(*s):
    msg(*s)
    msg('       \r')


SIZE = (20, 20)

def plot_coords(ax, xs, ys, color):
    ax.fill(xs, ys, color)


def plotitems(items):
    fig = pyplot.figure(1, figsize=SIZE, dpi=90)

    ax = fig.add_subplot(121)

    for item in items:
        color = '#{:06X}'.format(random.randint(0,0xffffff))
        x0, x1, y0, y1 = item.x0, item.x1, item.y0, item.y1
        text = item.get_text()[:10]
        plot_coords(ax, [x0, x1, x1, x0], [y0, y0, y1, y1], color)
        ax.text(x0, y0, text, fontsize=6)

    pyplot.show()

def plottextboxes(boxes):
    fig = pyplot.figure(1, figsize=SIZE, dpi=90)

    ax = fig.add_subplot(121)

    for box in boxes:
        color = '#{:06X}'.format(random.randint(0,0xffffff))
        for item in box.textlines:
            x0, x1, y0, y1 = item.x0, item.x1, item.y0, item.y1
            text = item.get_text()[:10]
            plot_coords(ax, [x0, x1, x1, x0], [y0, y0, y1, y1], color)
            ax.text(x0, y0, text, fontsize=6)

    pyplot.show()

def plottextblocks(blocks):
    fig = pyplot.figure(1, figsize=SIZE, dpi=90)

    ax = fig.add_subplot(121)

    for block in blocks:
        color = '#{:06X}'.format(random.randint(0,0xffffff))
        for tbox in block.textboxes:
            for item in tbox.textlines:
                x0, x1, y0, y1 = item.x0, item.x1, item.y0, item.y1
                text = item.get_text()[:10]
                plot_coords(ax, [x0, x1, x1, x0], [y0, y0, y1, y1], color)
                ax.text(x0, y0, text, fontsize=6)

    pyplot.show()

def isclose(a,b, atol=1e-05, rtol=1e-05):
    'test if two floats are "close"'
    "follows numpy.isclose"
    return abs(a - b) <= (atol + rtol * abs(b))


class ShapedTextBox:

    def __init__(self, textline):
        self.heading = None # if this is a heading - possible values True, False, None (i.e. dunno)
        self.textlines = [] # list of LTTextLine
        self.shape = None # shapely's shape of the box
        self.add(textline)

    def add(self, obj):
        DEBUG(3, 'add', repr(obj))
        if isinstance(obj, LTTextLine):
            #add a LTTextLine to the box, update shape
            x0, x1, y0, y1 = obj.x0, obj.x1, obj.y0, obj.y1
            box = shapely.geometry.box(x0, y0, x1, y1)
            self.textlines.append(obj)
            if self.shape is None:
                self.shape = box
            else:
                self.shape = self.shape.union(box)
        elif isinstance(obj, ShapedTextBox):
            self.textlines.extend(obj.textlines)
            if self.shape is None:
                self.shape = obj.shape
            else:
                self.shape = self.shape.union(obj.shape)
        else:
            print(repr(obj))
            raise NotImplementedError
        self.x0, self.y0, self.x1, self.y1 = self.shape.bounds

    def avg_lineheight(self):
        "average line height"
        avg = sum(abs(c.y1-c.y0) for c in self.textlines)/len(self.textlines)
        return avg

    def get_text(self):
        return self.textlines[0].get_text()

    def __repr__(self):
        return ('<%s(%s)>' %
                (self.__class__.__name__,self.textlines))


class ShapedTextLine:
    "LTTextLine with a lazily instantiated shape"
    def __init__(self, textline):
        self.textline = textline

    def __getattr__(self, name):
        if name == 'shape':
            line = self.textline
            x0, x1, y0, y1 = line.x0, line.x1, line.y0, line.y1
            self.shape = shapely.geometry.box(x0, y0, x1, y1)
            return self.shape
        else:
            return getattr(self.textline, name)

class TextBlock:
    """ArticleBlock corresponds typically to a newspaper article.
    It is a rectangular piece of page, containing several TextBoxes,
    typically with a heading (text in bigger font)
    """
    def __init__(self):
        self.textboxes = []
        self.shape = None

    def append(self, tbox):
        self.textboxes.append(tbox)
        if self.shape:
            self.shape = self.shape.union(tbox.shape)
        else:
            self.shape = tbox.shape
        self.bounds = self.shape.bounds

    def get_next_tbox(self, tbox, leftover):
        "find the nearest most appropriate text chunk from the list leftover"
        threshold = 0.5 # consider only chunks closer vertically than this (ratio of downward candidate text height)
        candidates = (x for x in leftover if tbox.shape.stance(x)<x.avg_lineheight()*threshold)
        candidates_below = [x for x in candidates if tbox.shape.bounds[1]>x.shape.bounds[1]]
        #pprint(candidates_below)
        if candidates_below:
            leftmost = min(candidates_below, key=lambda x:x.shape.bounds[0])
            return leftmost
        candidates_rightto = [x for x in candidates if tbox.shape.bounds[0]<x.shape.bounds[0]]
        if candidates_rightto:
            topmost = max(candidates_rightto, key=lambda x:x.shape.bounds[1])
            return topmost
        return None


    def sort_tboxes(self):
        "try to sort textboxes in this article by their geometric placement"
        chains = [] # list of chains of textboxes, in (hopefully) correct order
        leftover = sorted(self.textboxes, key=lambda x:-x.shape.bounds[3]) # not yet assigned textboxes
        while leftover:
            topmost = leftover[0] # the topmost one
            if topmost.heading:
                chain = [topmost]
                del leftover[0]
            else:
                diamost = min(leftover, key=lambda x:-x.shape.bounds[3]+x.shape.bounds[0])
                chain = [diamost]
                del leftover[leftover.index(diamost)]
            while True:
#                print 'ch-1', chain[-1]
                nxt = self.get_next_tbox(chain[-1], leftover)
                if nxt:
                    chain.append(nxt)
                    del leftover[leftover.index(nxt)]
                else:
                    break
            chains.append(chain)
            chain = []
        # now sort chains by their first textbox diagonal position
        chains = sorted(chains, key=lambda x:-x[0].shape.bounds[3]+x[0].shape.bounds[0])

        sorted_chunks = []
        for chain in chains:
            for tc in chain:
                sorted_tboxes.append(tc)
        self.textboxes = sorted_tboxes

    def stats(self):
        # return some statistics:
        # nr. of chunks, avg width, stdev width, avg height, stdev height
        nrchunks = len(self.textboxes)
        avgwidth = numpy.mean( [t.right-t.left for t in self.textboxes] )
        stdevwidth = numpy.std( [t.right-t.left for t in self.textboxes] )
        avgheight = numpy.mean( [t.height for t in self.textboxes] )
        stdevheight = numpy.std( [t.height for t in self.textboxes] )
        return nrchunks, avgwidth, stdevwidth, avgheight, stdevheight

    def get_text(self):
        return '\n¶\n'.join(x.get_text() for x in self.textboxes)

    def __str__(self):
        return '\n¶\n'.join(str(x) for x in self.textboxes)

class ShapeTextConverter(TextConverter):

    def __init__(self, rsrcmgr, outfp, codec='utf-8', pageno=1, laparams=None,
                 showpageno=False, imagewriter=None):
        TextConverter.__init__(self, rsrcmgr, outfp, codec=codec, pageno=pageno, laparams=laparams)
        self.showpageno = showpageno
        self.imagewriter = imagewriter
        self.textlines = []
        return

    def write_text(self, text):
        #self.outfp.write(text.encode(self.codec, 'ignore'))
        return

    def receive_layout(self, ltpage):
        def render(item):
            reject = False
            r = ''
            if isinstance(item, LTTextLine):
                if debuglevel >= 1:
                    msg('.')
                linestr = ''
                reject = False
                for child in item:
                    child_text, child_status = render(child)
                    if not child_status: #this signals rejection
                        reject = True
                    linestr += child_text
                if not reject:
                    self.textlines.append(item)
                else:
                    DEBUG(1, 'REJECTED:', linestr)
            elif isinstance(item, LTContainer):
                for child in item:
                    child_text, child_status = render(child)
                    if child_status:
                        r += child_text
            elif isinstance(item, LTText):
                item_text = item.get_text()
                r += item_text
                self.write_text(item.get_text())
                if isinstance(item, LTChar):
                    a,b,c,d,x,y = item.matrix
                    phi1 = atan2(c,d)
                    phi2 = -atan2(b,a)
                    if not isclose(phi1,phi2, atol=options.shear_limit,rtol=options.shear_limit):
                        DEBUG(2, 'SHEAR', phi1, phi2, item_text)
                        reject = True
                    if max(abs(phi1), abs(phi2)) > options.rotation_limit*pi/180:
                        DEBUG(2, 'ROT', phi1, phi2, item_text)
                        reject = True
                    if not isinstance(item_text, unicode):
                        DEBUG(2, 'NOT UNICODE', repr(item_text))
                        reject = True
            if isinstance(item, LTTextBox):
                r += '\n'
                self.write_text('\n')
            elif isinstance(item, LTImage):
                if self.imagewriter is not None:
                    self.imagewriter.export_image(item)
            return r, not reject

        if self.showpageno:
            self.write_text('Page %s\n' % ltpage.pageid)
        render(ltpage)
        msgn()
        self.write_text('\f')
        return

    # Some dummy functions to save memory/CPU when all that is wanted
    # is text.  This stops all the image and drawing ouput from being
    # recorded and taking up RAM.
    def render_image(self, name, stream):
        if self.imagewriter is None:
            return
        PDFConverter.render_image(self, name, stream)
        return

    def paint_path(self, gstate, stroke, fill, evenodd, path):
        return


def get_next_textline(textline, leftover):
    "find the nearest most appropriate textline from the list leftover"
    threshold = 0.5 # consider only chunks closer vertically than this (ratio of downward candidate text height)
    candidates = (x for x in leftover if x != textline and  textline.shape.distance(x.shape)<abs(x.shape.bounds[3]-x.shape.bounds[1])*threshold)
    candidates_below = [x for x in candidates if textline.shape.bounds[1]>x.shape.bounds[1]]
    #pprint(candidates_below)
    if candidates_below:
        leftmost = min(candidates_below, key=lambda x:x.shape.bounds[0])
        return leftmost
    candidates_rightto = [x for x in candidates if textline.shape.bounds[0]<x.shape.bounds[0]]
    if candidates_rightto:
        topmost = max(candidates_rightto, key=lambda x:x.shape.bounds[1])
        return topmost
    return None


def get_text_boxes(textlines):
    # convert all textlines to textboxes
    textboxes = [ShapedTextBox(x) for x in textlines]
    DEBUG(2, 'got', len(textlines), 'textlines, grouping...')
    reduced = True
    while reduced:
        reduced = False
        i = 0
        while i < len(textboxes):
            box1 = textboxes[i]
            j = i
            while j < len(textboxes):
                if debuglevel >= 2:
                    msgr(i, j, len(textboxes))
#                print(i, j, len(textboxes))
                #pprint(textboxes)
                box2 = textboxes[j]
                left1, bottom1, right1, top1 = box1.shape.bounds
                left2, bottom2, right2, top2 = box2.shape.bounds
                lineheight1 = box1.avg_lineheight()
                lineheight2 = box2.avg_lineheight()

                # o kolko mozu byt riadky od seba vertikalne v absolutnej hodnote, aby to este nebolo chapane ako prazdny riadok
                mls = options.line_margin * (lineheight1 + lineheight2) / 2
#                mcs = options.max_char_spread*(lineheight1 + lineheight2) / 2
                if (
                    (i!=j) and
                    # riadky maju podobnu vysku
                    abs(lineheight1 - lineheight2) / ((lineheight1 + lineheight2)/2) < options.line_height_diff and
                    # bloky sa vertikalne prekryvaju alebo su blizko k sebe
                    (
                        (bottom2-mls <= bottom1 <= top2+mls) or (bottom1-mls <= bottom2 <= top1+mls)
                    ) and
#                    (
#                        box1.shape.distance(box2.shape) < mcs
#                    ) and

                    # bloky sa horizontalne prekryvaju
                    ( (left2 <= left1 <= right2) or (left1 <= left2 <= right1) )
                    ):
                    box1.add(box2)
                    del textboxes[j]
                    reduced = True
                else:
                    j += 1
            i += 1
        if debuglevel>=2:
            msgn('')
    textboxes = sorted(textboxes, key=lambda x:x.shape.bounds[3], reverse=True)

    return textboxes


def get_avg_linegeight(text_boxes):
    "calculate average line height"
    sum_lh = 0
    sum_chars = 0
    for tbox in text_boxes:
        for tline in tbox.textlines:
            l = len(tline.get_text())
            sum_lh += l * abs(tline.y1-tline.y0)
            sum_chars += l
    avg = 1. * sum_lh / sum_chars
    return avg


def get_article_blocks(text_boxes):
    avg_lineheight = get_avg_linegeight(text_boxes)
    article_blocks = []
    text_boxes_in_article_blocks = set() # keep track of already assigned text boxes
    i = 0
    text_boxes_c = copy.copy(text_boxes)
    while i < len(text_boxes_c):
        tc = text_boxes_c[i]
        if tc.avg_lineheight() > avg_lineheight *1.5:
            tc.heading = True
            a = TextBlock()
            a.append(tc)
            text_boxes_in_article_blocks.add(tc)
            del text_boxes_c[i]
            article_blocks.append(a)
            msg('.')
        else:
            tc.heading = False
            i += 1


    msg('!')
    process_article_blocks = copy.copy(article_blocks)

    text_boxes_remaining = set(text_boxes)
    text_boxes_remaining = list(text_boxes_remaining)

    while text_boxes_remaining:
        msg('.')
        # now, add to each ArticleBlock everything that is below, until another heading is encountered

        text_boxes_remaining.sort(key=lambda x: -x.shape.bounds[1]) # sort by bottom coordinate
        for ab in process_article_blocks:
            ab_left, ab_bottom, ab_right, ab_top = ab.bounds
            bottom = ab_bottom
            while bottom >=0: # LOOP #1
                bottom -= 1
                newbox = shapely.geometry.box(ab_left, bottom, ab_right, ab_top)
                i = 0
                while i < len(text_boxes_remaining):
                    tc = text_boxes_remaining[i]
                    if tc.shape.bounds[1] > ab_bottom or tc in ab.textboxes:
                        # boxes above our header
                        i += 1
                        continue
                    if tc.shape.intersects(newbox):
                        if tc.avg_lineheight() > avg_lineheight *1.5:
                            tc.heading = True
                            # new header enountered, stop here
                            bottom = -1 # signal end of LOOP #1
                            break
                        else:
                            tc.heading = False
                            ab.append(tc)
                            text_boxes_in_article_blocks.add(tc)
                            del text_boxes_remaining[i]
                    else:
                        i += 1

        text_boxes_remaining = set(text_boxes_remaining) - text_boxes_in_article_blocks
        text_boxes_remaining = list(text_boxes_remaining)
        if not text_boxes_remaining:
            break
        # find leftmost top of remaining text boxes (those without heading)
        # with some left-right fuzzyness to allow for uneven left margins
        leftmost = text_boxes_remaining[0]
        leftmost_index = 0
        for i in range(1, len(text_boxes_remaining)):
            tc = text_boxes_remaining[i]
            tc_width = tc.shape.bounds[2] - tc.shape.bounds[0]
            leftmost_width = leftmost.shape.bounds[2] - leftmost.shape.bounds[0]
            assert tc_width > 0
            assert leftmost_width > 0

            # if the new chunk is more than 10% of the smaller of (new_chunk, old_chunk) from
            # the old position, let it be the leftmost one
            if tc.shape.bounds[0] < leftmost.shape.bounds[0] - 0.1*min(tc_width, leftmost_width):
                leftmost = tc
                leftmost_index = i
            # if it is withing 10%, use the higher placed one
            elif abs(tc.shape.bounds[0] - leftmost.shape.bounds[0]) < 0.1*min(tc_width, leftmost_width):
                if tc.shape.bounds[3] > leftmost.shape.bounds[3]:
                    leftmost = tc
                    leftmost_index = i

        a = TextBlock()
        a.append(leftmost)
        article_blocks.append(a)
        text_boxes_in_article_blocks.add(leftmost)
    msgn('!')
    return article_blocks

# main
def main(argv):

    # debug option
    debug = 0
    # input option
    password = ''
    pagenos = set()
    maxpages = 0
    # output option
    outfile = None
    outtype = None
    imagewriter = None
    rotation = 0
    stripcontrol = False
    layoutmode = 'normal'
    codec = 'utf-8'
    pageno = 1
    scale = 1
    caching = True
    showpageno = True
    laparams = LAParams()
    using_optparse = False

    parser = ArgumentParser(prog='pdf2txt.py',
            description='Convert pdf to txt',
            formatter_class=ArgumentDefaultsHelpFormatter)

    if using_optparse:
        DEBUG(3, 'using optparse')
        parser.add_argument = parser.add_option
        parser.parse_known_args = parser.parse_args
        parser.disable_interspersed_args()

    parser.add_argument('-d', dest='debuglevel', action='count',
                       default = 0,
                       help='Debug (repeat for more verbose debugging)')

    parser.add_argument('-p', '--pages', dest='pagenos', action='store',
                       type=str,
                       default = '',
                       help='Specifies the comma-separated list of the page numbers to be extracted. Page numbers start at one. By default, it extracts text from all the pages.')

    parser.add_argument('-c', '--codec', dest='codec', action='store',
                       type=str,
                       default='utf-8',
                       help='Specifies the output codec.')

    parser.add_argument('-t', '--type', dest='outtype', action='store',
                       type=str,
                       default='shape',
                       choices = ['text', 'html', 'xml', 'tag', 'shape'],
                       help='Specifies the output format, one of: shape, text, html, xml, tag')

    parser.add_argument('-m', dest='maxpages', action='store',
                       type=int,
                       default=0,
                       help='Specifies the maximum number of pages to extract. By default (0), it extracts all the pages in a document.')

    parser.add_argument('-P', '--password', dest='password', action='store',
                       type=str,
                       default='',
                       help='Provides the user password to access PDF contents.')

    parser.add_argument('-o', '--output', dest='outfile', action='store',
                       type=str,
                       default=None,
                       help='Specifies the output file name. By default, it prints the extracted contents to stdout in text format.')

    parser.add_argument('-C', '--no-caching', dest='caching', action='store_false',
                       default=True,
                       help='Suppress object caching. This will reduce the memory consumption but also slows down the process.')

    parser.add_argument('-n', '--no-layout', dest='layout', action='store_false',
                       default=True,
                       help='Suppress layout analysis.')


    parser.add_argument('-A', '--analyze-all', dest='all_texts', action='store_true',
                       default=False,
                       help='Forces to perform layout analysis for all the text strings, including text contained in figures.')

    parser.add_argument('-V', '--detect-vertical', dest='detect_vertical', action='store_true',
                       default=False,
                       help='Allows vertical writing detection.')

    parser.add_argument('-M', dest='char_margin', action='store',
                       type=float,
                       default=2.0,
                       help='Two text chunks whose distance is closer than the char_margin (shown as M) is considered continuous and get grouped into one.')

    parser.add_argument('-L', dest='line_margin', action='store',
                       type=float,
                       default=0.5,
                       help='Two lines whose distance is closer than the line_margin (L) is grouped as a text box, which is a rectangular area that contains a "cluster" of text portions.')

    parser.add_argument('-W', dest='word_margin', action='store',
                       type=float,
                       default=0.1,
                       help='It may be required to insert blank characters (spaces) as necessary if the distance between two words is greater than the word_margin (W), as a blank between words might not be represented as a space, but indicated by the positioning of each word.')

    parser.add_argument('-F', dest='boxes_flow', action='store',
                       type=float,
                       default=0.5,
                       help='Specifies how much a horizontal and vertical position of a text matters when determining a text order. The value should be within the range of -1.0 (only horizontal position matters) to +1.0 (only vertical position matters).')


    parser.add_argument('-Y', '--layout-mode', dest='layoutmode', action='store',
                       type=str,
                       default='normal',
                       choices = ['exact', 'normal', 'loose'],
                       help='Specifies how the page layout should be preserved. (Currently only applies to HTML format.) One of: exact, normal, loose.')

    parser.add_argument('-O', '--image-writer', dest='imagewriter', action='store',
                       type=str,
                       default=None,
                       help='imagewriter')

    parser.add_argument('-R', '--rotation', dest='rotation', action='store',
                       type=int,
                       default=0,
                       help='rotation')

    parser.add_argument('-S', '--strip-control', dest='stripcontrol', action='store_true',
                       default=False,
                       help='stripcontrol')

    parser.add_argument('-s', dest='scale', action='store',
                       type=float,
                       default=1,
                       help='Specifies the output scale. Can be used in HTML format only.')

    parser.add_argument('--draw-lines', dest='draw_lines', action='store_true',
                       help="Draw crude page representation, coloured TextLines (= short pieces of text). Valid only for the `shape' output.")

    parser.add_argument('--draw-boxes', dest='draw_boxes', action='store_true',
                       help="Draw crude page representation, coloured TextBoxes (= grouped text lines). Valid only for the `shape' output.")

    parser.add_argument('--draw-blocks', dest='draw_blocks', action='store_true',
                       help="Draw crude page representation, coloured TextBlocks (= grouped TextBoxes). Valid only for the `shape' output.")

    parser.add_argument('--shear-limit', dest='shear_limit', action='store',
                        default=0.1,
                        type=float,
                        help="If the text is sheared above this limit, reject it. Valid only for the `shape' output.")

    parser.add_argument('--rotation-limit', dest='rotation_limit', action='store',
                        default=2,
                        type=float,
                        help="If the text is rotated above this angle (in degrees), reject it. Valid only for the `shape' output.")

    parser.add_argument('--line-height-diff', dest='line_height_diff', action='store',
                       type=float,
                       default=0.1,
                       help='Two lines whose vertical sizes differ more than this ratio are not to be considered of the same paragraph (but e.g. one of them is a heading).')


    args, rest = parser.parse_known_args()

    global debuglevel
    debuglevel = debug = args.debuglevel
    DEBUG(3, 'args:', str(args))
    DEBUG(3, 'rest:', str(rest))

    DEBUG(3, 'optparse:', using_optparse)

    if args.pagenos:
        pagenos.update( int(x)-1 for x in args.pagenos.split(',') )
    maxpages = args.maxpages
    outfile = args.outfile
    password = args.password
    caching = args.caching
    if not args.layout:
        laparams = None
    if laparams and args.all_texts:
        laparams.all_texts = True
    if laparams and args.detect_vertical:
        laparams.detect_vertical = True
    if laparams:
        laparams.char_margin = args.char_margin
        laparams.line_margin = args.line_margin
        laparams.word_margin = args.word_margin
        laparams.boxes_flow = args.boxes_flow
    layoutmode = args.layoutmode

    if args.imagewriter:
        imagewriter = ImageWriter(args.imagewriter)

    rotation = args.rotation
    stripcontrol = args.stripcontrol
    outtype = args.outtype
    codec = args.codec
    scale = args.scale

    global options
    options = args

    PDFDocument.debug = debug
    PDFParser.debug = debug
    CMapDB.debug = debug
    PDFPageInterpreter.debug = debug

    rsrcmgr = PDFResourceManager(caching=caching)
    if not outtype:
        outtype = 'text'
        if outfile:
            if outfile.endswith('.htm') or outfile.endswith('.html'):
                outtype = 'html'
            elif outfile.endswith('.xml'):
                outtype = 'xml'
            elif outfile.endswith('.tag'):
                outtype = 'tag'
    if outfile:
        outfp = file(outfile, 'w')
    else:
        outfp = sys.stdout
    if outtype == 'shape':
        device = ShapeTextConverter(rsrcmgr, outfp, codec=codec, laparams=laparams,
                               imagewriter=imagewriter)
    elif outtype == 'text':
        device = TextConverter(rsrcmgr, outfp, codec=codec, laparams=laparams,
                               imagewriter=imagewriter)
    elif outtype == 'xml':
        device = XMLConverter(rsrcmgr, outfp, codec=codec, laparams=laparams,
                              imagewriter=imagewriter,
                              stripcontrol=stripcontrol)
    elif outtype == 'html':
        device = HTMLConverter(rsrcmgr, outfp, codec=codec, scale=scale,
                               layoutmode=layoutmode, laparams=laparams,
                               imagewriter=imagewriter, debug=debug)
    elif outtype == 'tag':
        device = TagExtractor(rsrcmgr, outfp, codec=codec)
    else:
        return usage()
    for fname in rest:
        fp = file(fname, 'rb')
        interpreter = PDFPageInterpreter(rsrcmgr, device)
        for page in PDFPage.get_pages(fp, pagenos,
                                      maxpages=maxpages, password=password,
                                      caching=caching, check_extractable=True):
            page.rotate = (page.rotate+rotation) % 360
            interpreter.process_page(page)
        fp.close()
    device.close()
    textboxes = get_text_boxes(device.textlines)

    textblocks = get_article_blocks(textboxes)
    if args.draw_lines:
        plotitems(device.textlines)
    if args.draw_boxes:
        plottextboxes(textboxes)
    if args.draw_blocks:
        plottextblocks(textblocks)
    outfp.close()
    return

if __name__ == '__main__':
    sys.exit(main(sys.argv))


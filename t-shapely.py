#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import print_function

import sys
reload(sys)
sys.setdefaultencoding('UTF8')

import re, unicodedata, copy
from pprint import pprint

import random
import argparse

from pdfminer.pdfdocument import PDFDocument, PDFNoOutlines
from pdfminer.pdfparser import PDFParser
from pdfminer.pdfinterp import PDFResourceManager, PDFPageInterpreter
from pdfminer.converter import PDFPageAggregator
from pdfminer.layout import LTPage, LTChar, LTAnno, LAParams, LTTextBox, LTTextLine
from pdfminer.pdfpage import PDFPage


from matplotlib import pyplot
import shapely.geometry
import numpy

from math import atan2, pi

import codecs
sys.stdout = codecs.getwriter('utf-8')(sys.stdout)

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


class TBox:
    "box with a text, the basic building block of text page with layout"
    def __init__(self, x1, y1, x2, y2, text='', page_number=None):
        self.text = text
        self.page_number = page_number
        self.box = shapely.geometry.box(x1, y1, x2, y2)
        self.bounds = self.box.bounds
        self.exterior = self.box.exterior
        width = self.bounds[2] - self.bounds[0]
        avg_chw = len(text)/float(width)
        print('fasz', len(text), avg_chw, self.bounds[3]-self.bounds[1], text)

    def union(self, other):
        assert self.page_number == other.page_number
        rtext = self.text+' '+other.text #FIXME test order by x
        rbox = self.box.union(other.box)
        x1, y1, x2, y2 = rbox.bounds
        rtbox = TBox(x1, y1, x2, y2, rtext, self.page_number)
        return rtbox

    def __str__(self):
        return self.text

    def __repr__(self):
        x1, y1, x2, y2 = self.bounds
        text = self.text
        return u'TBox({x1:3.0f}, {y1:3.0f}, {x2:3.0f}, {y2:3.0f}, {text}'.format(**locals())

SIZE = (20, 20)


def plot_coords(ax, ob, color):
    x, y = ob.xy
#    ax.plot(x, y, 'b-', color=color, zorder=1)
    ax.fill(x, y, color)


def plotchunks(tchunks):
    fig = pyplot.figure(1, figsize=SIZE, dpi=90)

    ax = fig.add_subplot(121)

    for tchunk in tchunks:
        color = '#{:06X}'.format(random.randint(0,0xffffff))
        for tbox in tchunk.tboxes:
            plot_coords(ax, tbox.box.boundary, color)
            xmin, ymin, xmax, ymax = tbox.bounds
            ax.text(xmin, ymin, tbox.text, fontsize=6)

    pyplot.show()


def plotblocks(blocks):
    fig = pyplot.figure(1, figsize=SIZE, dpi=90)

    ax = fig.add_subplot(121)

    for block in blocks:
        color = '#{:06X}'.format(random.randint(0,0xffffff))
        for tchunk in block.tchunks:
            for tbox in tchunk.tboxes:
                plot_coords(ax, tbox.box.boundary, color)
                xmin, ymin, xmax, ymax = tchunk.polygon.bounds
                ax.text(xmin, ymin, tbox.text, fontsize=6)
    pyplot.show()



_lig_table = {
        u'ﬁ': 'fi',
        u'ﬂ': 'fl',
        }

_lig_re = u'|'.join(lig for lig in _lig_table)
_lig_re = u'({ligs}) '.format(ligs = _lig_re)

def fixlig(txt):
    "fix ligatures"
    r = re.sub(_lig_re, lambda x: _lig_table[x.group(1)], txt)
    return r

def is_lowercase(c):
    "test if text is lowercase"
    return c.upper() != c

def is_letter(c):
    return unicodedata.category(c)[0] in 'L'

def isclose(a,b, atol=1e-05, rtol=1e-05):
    'test if two floats are "close"'
    "follows numpy.isclose"
    return abs(a - b) <= (atol + rtol * abs(b))

def fixhyp(txt):
    lines = txt.splitlines()
    newlines = [lines[0]]
    for l in lines[1:]:
        prevline = newlines[-1]
        if prevline.endswith('-') and len(prevline)>=2 and is_letter(prevline[-2]) and (l and is_lowercase(l[0])):
            newlines[-1] = prevline[:-1] + l
        else:
            newlines.append(l)
    return '\n'.join(newlines)

class PDFPageDetailedAggregator(PDFPageAggregator):
    def __init__(self, rsrcmgr, pageno=1, laparams=None):
        PDFPageAggregator.__init__(self, rsrcmgr, pageno=pageno, laparams=laparams)
        self.rows = []
        self.page_number = 0

    def receive_layout(self, ltpage):
        def render(item, page_number):
            if isinstance(item, LTPage) or isinstance(item, LTTextBox):
                for child in item:
                    render(child, page_number)
            elif isinstance(item, LTTextLine):
                DEBUG(3, item)
                child_str = ''
                reject = False
                for child in item:
                    if isinstance(child, (LTChar, LTAnno)):
                        DEBUG(4, child)
                        child_text = child.get_text()
                        if isinstance(child, LTChar):
                            a,b,c,d,x,y = child.matrix
                            phi1 = atan2(c,d)
                            phi2 = -atan2(b,a)
                            if not isclose(phi1,phi2, atol=options.shear_limit,rtol=options.shear_limit):
                                DEBUG(2, 'SHEAR', phi1, phi2, child_text)
                                reject = True
                                #break
                            if max(abs(phi1), abs(phi2)) > options.rotation_limit*pi/180:
                                DEBUG(2, 'ROT', phi1, phi2, child_text)
                                reject = True
                                #break
                            if not isinstance(child_text, unicode):
                                DEBUG(2, 'NOT UNICODE', repr(child_text))
                                reject = True
                        if isinstance(child_text, unicode):
                            child_str += child_text
                        elif isinstance(child_text, str):
                            child_str += unicode(child_text, 'utf-8')
                        else:
                            child_str += 'WTF'+repr(child_text)
                if reject:
                    DEBUG(1, 'REJECT', repr(child_str))
                    child_str = ''
                child_str = ' '.join(child_str.split()).strip()
                if child_str:
                    x1, y1, x2, y2 = item.bbox
                    row = TBox(x1, y1, x2, y2, child_str, page_number)
                    self.rows.append(row)
                for child in item:
                    render(child, page_number)
            return
        render(ltpage, self.page_number)
        self.page_number += 1
        self.result = ltpage



class TChunk:
    "keeps a list of TBox'es and a corresponding shapely object as their union"
    def __init__(self, tbox=None):
        self.heading = None # if this is a heading - possible values True, False, None (i.e. dunno)
        if tbox:
            self.tboxes = [tbox]
            self.page_number = tbox.page_number
            self.polygon = tbox.box

            bounds = tbox.bounds
            self.bottom = bounds[1]
            self.left = bounds[0]
            self.top = bounds[3]
            self.right = bounds[2]
            self.height = self.lineheight = self.top - self.bottom
            self.text = None
            assert self.height > 0
            assert self.bottom < self.top and self.left < self.right
        else:
            self.tboxes = []
            self.page_number = None
            self.bottom = self.top = self.left = self.right = self.height = self.lineheigh = 0

    def append(self, tbox):
        if self.page_number is not None:
            assert self.page_number == tbox.page_number
        else:
            self.page_number = tbox.page_number
        self.tboxes.append(tbox)
        self.polygon = self.polygon.union(tbox.box)
        self.lineheight = sum(c.bounds[3]-c.bounds[1] for c in self.tboxes)/len(self.tboxes)
        self.height = max(c.bounds[3] for c in self.tboxes) - min(c.bounds[1] for c in self.tboxes)
        assert self.height > 0
        if tbox.bounds[0] < self.left:
            self.left = tbox.bounds[0]
        if tbox.bounds[2] > self.right:
            self.right = tbox.bounds[2]
        if tbox.bounds[1] < self.bottom:
            self.bottom = tbox.bounds[1]
        if tbox.bounds[3] > self.top:
            self.top = tbox.bounds[3]
        assert self.bottom < self.top and self.left < self.right
#        self.mean_left = sum(c[0] for c in self.chunks) / len(self)
#        self.mean_right = sum(c[2] for c in self.chunks) / len(self)
#        assert self.mean_left < self.mean_right

    def extend(self, tboxes):
        for t in tboxes:
            self.append(t)

    def distance(self, other):
        return self.polygon.distance(other.polygon)

    def get_lines(self):
        lines = []
        # sort text boxes by their y coordinate first
        boxes_by_y = {}
        for tb in self.tboxes:
            y1 = tb.bounds[1]
            if y1 in boxes_by_y:
                boxes_by_y[y1].append(tb)
            else:
                boxes_by_y[y1] = [tb]
        # teraz zlucime chunky s podobnym y
        keys = sorted(boxes_by_y.keys(), reverse=True)
        i = 0
        while i < len(keys)-1:
            # ak sa y-nova suradnica lisi menej nez o iste percento vysky riadku, povazujeme to za jeden riadok
            if abs(keys[i] - keys[i+1]) / self.lineheight < 0.1: #FIXME parameter
                y1 = keys[i]
                y2 = keys[i+1] # y-ova suradnica druheho chunku
                boxes_by_y[y1].extend(boxes_by_y[y2])
                del boxes_by_y[y2]
                del keys[i+1]
            i += 1
        for k in keys:
            boxes_at_line = boxes_by_y[k] # all the boxes within one line
#            chunks_by_y[k].sort() # podla x-ovej suradnice
            boxes_by_y[k].sort(key=lambda x: x.bounds[0])
            # get bouding box of the line
            line = boxes_at_line[0]
            for i in range(1, len(boxes_at_line)):
                line = line.union(boxes_at_line[i])
            lines.append(line)
        return lines

    def get_text(self):
        if self.text is not None:
            return self.text
        lines = self.get_lines()
        textlines = (x.text for x in lines)
        text = '\n'.join(textlines) 
        text = fixlig(text)
        text = fixhyp(text)
        self.text = text
        return text


    def __len__(self):
        return len(self.tboxes)

    def __str__(self):
        return '\n '.join(str(x) for x in self.tboxes)

    def __repr__(self):
        return 'L: {lh:3.1f} {s}'.format(lh=self.lineheight, s=' '.join(repr(c) for c in self.tboxes))

class ArticleBlock:
    """ArticleBlock corresponds typically to a newspaper article.
    It is a rectangular piece of page, containing several TChunks,
    typically with a heading (text in bigger font)
    """
    def __init__(self):
        self.tchunks = []
        self.polygon = None

    def append(self, tchunk):
        self.tchunks.append(tchunk)
        if self.polygon:
            self.polygon = self.polygon.union(tchunk.polygon)
        else:
            self.polygon = tchunk.polygon
        self.bounds = self.polygon.bounds

    def get_next_chunk(self, tchunk, leftover):
        "find the nearest most appropriate text chunk from the list leftover"
        threshold = 0.5 # consider only chunks closer vertically than this (ratio of downward candidate text height)
        candidates = (x for x in leftover if tchunk.distance(x)<x.lineheight*threshold)
        candidates_below = [x for x in candidates if tchunk.polygon.bounds[1]>x.polygon.bounds[1]]
        #pprint(candidates_below)
        if candidates_below:
            leftmost = min(candidates_below, key=lambda x:x.polygon.bounds[0])
            return leftmost
        candidates_rightto = [x for x in candidates if tchunk.polygon.bounds[0]<x.polygon.bounds[0]]
        if candidates_rightto:
            topmost = max(candidates_rightto, key=lambda x:x.polygon.bounds[1])
            return topmost
        return None


    def sort_chunks(self):
        "try to sort chunks in this article by their geometric placement"
        chains = [] # list of chains of tchunks, in (hopefully) correct order
        leftover = sorted(self.tchunks, key=lambda x:-x.polygon.bounds[3]) # not yet assigned chunks
        while leftover:
            topmost = leftover[0] # the topmost one
            if topmost.heading:
                chain = [topmost]
                del leftover[0]
            else:
                diamost = min(leftover, key=lambda x:-x.polygon.bounds[3]+x.polygon.bounds[0])
                chain = [diamost]
                del leftover[leftover.index(diamost)]
            while True:
#                print 'ch-1', chain[-1]
                nxt = self.get_next_chunk(chain[-1], leftover)
                if nxt:
                    chain.append(nxt)
                    del leftover[leftover.index(nxt)]
                else:
                    break
            chains.append(chain)
            chain = []
        # now sort chains by their first chunk diagonal position
        chains = sorted(chains, key=lambda x:-x[0].polygon.bounds[3]+x[0].polygon.bounds[0])

        sorted_chunks = []
        for chain in chains:
            for tc in chain:
                sorted_chunks.append(tc)
        self.tchunks = sorted_chunks

    def stats(self):
        # return some statistics:
        # nr. of chunks, avg width, stdev width, avg height, stdev height
        nrchunks = len(self.tchunks)
        avgwidth = numpy.mean( [t.right-t.left for t in self.tchunks] )
        stdevwidth = numpy.std( [t.right-t.left for t in self.tchunks] )
        avgheight = numpy.mean( [t.height for t in self.tchunks] )
        stdevheight = numpy.std( [t.height for t in self.tchunks] )
        return nrchunks, avgwidth, stdevwidth, avgheight, stdevheight

    def get_text(self):
        return '\n¶\n'.join(x.get_text() for x in self.tchunks)

    def __str__(self):
        return '\n¶\n'.join(str(x) for x in self.tchunks)


def get_avg_linegeight(text_chunks):
    "calculate average line height"
    sum_lh = 0
    sum_chars = 0
    for chunk in text_chunks:
        l = len(chunk.get_text())
        sum_lh += l * chunk.lineheight
        sum_chars += l
    avg = 1. * sum_lh / sum_chars
    return avg


def get_text_chunks(fname):
    DEBUG(3, 'Opening file', fname)
    fp = open(fname, 'rb')
    parser = PDFParser(fp)
    doc = PDFDocument(parser)
    #doc.initialize('password') # leave empty for no password

    rsrcmgr = PDFResourceManager()
    laparams = LAParams()
    laparams.char_margin = 0.6
    laparams.word_margin = 0.9
    laparams.line_margin = 0.9

    device = PDFPageDetailedAggregator(rsrcmgr, laparams=laparams)
    interpreter = PDFPageInterpreter(rsrcmgr, device)

    text_chunks = []

    pagenumber = 0
    for page in PDFPage.create_pages(doc):
        #print '@@@ PG:', pagenumber
        DEBUG(1, 'page:', pagenumber)
        interpreter.process_page(page)
        # receive the LTPage object for this page
        pagenumber += 1


    device.get_result()
    for row in device.rows:
        text_chunks.append( TChunk(row) )

    DEBUG(1, 'got results, chunks:', len(device.rows), len(text_chunks))

    text_chunks_by_pg = {}
    for tc in text_chunks:
        pg = tc.page_number
        if pg in text_chunks_by_pg:
            text_chunks_by_pg[pg].append(tc)
        else:
            text_chunks_by_pg[pg] = [tc]

    pages = sorted(text_chunks_by_pg.keys())

    del text_chunks

    for page in pages:
        text_chunks = text_chunks_by_pg[page]
        reduced = True
        while reduced:
            reduced = False
            i = 0
            while i < len(text_chunks):
                chunk1 = text_chunks[i]
                j = i
                while j < len(text_chunks):
                    msgr(i, j, len(text_chunks))
                    chunk2 = text_chunks[j]
                    assert chunk1.page_number == chunk2.page_number
                    # o kolko mozu byt bloky od seba vertikalne v absolutnej hodnote, aby to este nebolo chapane ako prazdny riadok
                    mls = (options.max_line_spread - 1) * (chunk1.lineheight + chunk2.lineheight) / 2
                    mcs = options.max_char_spread*(chunk1.lineheight + chunk2.lineheight) / 2
                    if (
                        (i!=j) and
                        # riadky maju podobnu vysku
                        abs(chunk1.lineheight - chunk2.lineheight) / ((chunk1.lineheight + chunk2.lineheight)/2) < options.line_height_diff and
                        # bloky sa vertikalne prekryvaju alebo su blizko k sebe
                        (
                            (chunk2.bottom-mls <= chunk1.bottom <= chunk2.top+mls) or (chunk1.bottom-mls <= chunk2.bottom <= chunk1.top+mls)
                        ) and
                        (
                            chunk1.distance(chunk2) < mcs
                        ) and

                        # bloky sa horizontalne prekryvaju
                        ( (chunk2.left <= chunk1.left <= chunk2.right) or (chunk1.left <= chunk2.left <= chunk1.right) )
                        ):
                        chunk1.extend(chunk2.tboxes)
                        del text_chunks[j]
                        reduced = True
                    else:
                        j += 1
                i += 1

            msgn('')
        blocks = []
        text_chunks = sorted(text_chunks, key=lambda x:x.top, reverse=True)

        yield text_chunks # per page



def get_article_blocks(text_chunks):
    avg_lineheight = get_avg_linegeight(text_chunks)
    article_blocks = []
    text_chunks_in_article_blocks = set() # keep track of already assigned text chunks
    i = 0
    text_chunks_c = copy.copy(text_chunks)
    while i < len(text_chunks_c):
        tc = text_chunks_c[i]
        if tc.lineheight > avg_lineheight *1.5:
            tc.heading = True
            a = ArticleBlock()
            a.append(tc)
            text_chunks_in_article_blocks.add(tc)
            del text_chunks_c[i]
            article_blocks.append(a)
            msg('.')
        else:
            tc.heading = False
            i += 1


    msg('!')
    process_article_blocks = copy.copy(article_blocks)

    text_chunks_remaining = set(text_chunks)
    text_chunks_remaining = list(text_chunks_remaining)

    while text_chunks_remaining:
        msg('.')
        # now, add to each ArticleBlock everything that is below, until another heading is encountered

        text_chunks_remaining.sort(key=lambda x: -x.polygon.bounds[1]) # sort by bottom coordinate
        for ab in process_article_blocks:
            ab_left, ab_bottom, ab_right, ab_top = ab.bounds
            bottom = ab_bottom
            while bottom >=0: # LOOP #1
                bottom -= 1
                newbox = shapely.geometry.box(ab_left, bottom, ab_right, ab_top)
                i = 0
                while i < len(text_chunks_remaining):
                    tc = text_chunks_remaining[i]
                    if tc.polygon.bounds[1] > ab_bottom or tc in ab.tchunks:
                        # chunks above our header
                        i += 1
                        continue
                    if tc.polygon.intersects(newbox):
                        if tc.lineheight > avg_lineheight *1.5:
                            tc.heading = True
                            # new header enountered, stop here
                            bottom = -1 # signal end of LOOP #1
                            break
                        else:
                            tc.heading = False
                            ab.append(tc)
                            text_chunks_in_article_blocks.add(tc)
                            del text_chunks_remaining[i]
                    else:
                        i += 1

        text_chunks_remaining = set(text_chunks_remaining) - text_chunks_in_article_blocks
        text_chunks_remaining = list(text_chunks_remaining)
        if not text_chunks_remaining:
            break
        # find leftmost top of remaining text chunks (those without heading)
        # with some left-right fuzzyness to allow for uneven left margins
        leftmost = text_chunks_remaining[0]
        leftmost_index = 0
        for i in range(1, len(text_chunks_remaining)):
            tc = text_chunks_remaining[i]
            tc_width = tc.polygon.bounds[2] - tc.polygon.bounds[0]
            leftmost_width = leftmost.polygon.bounds[2] - leftmost.polygon.bounds[0]
            assert tc_width > 0
            assert leftmost_width > 0

            # if the new chunk is more than 10% of the smaller of (new_chunk, old_chunk) from
            # the old position, let it be the leftmost one
            if tc.polygon.bounds[0] < leftmost.polygon.bounds[0] - 0.1*min(tc_width, leftmost_width):
                leftmost = tc
                leftmost_index = i
            # if it is withing 10%, use the higher placed one
            elif abs(tc.polygon.bounds[0] - leftmost.polygon.bounds[0]) < 0.1*min(tc_width, leftmost_width):
                if tc.polygon.bounds[3] > leftmost.polygon.bounds[3]:
                    leftmost = tc
                    leftmost_index = i

        a = ArticleBlock()
        a.append(leftmost)
        article_blocks.append(a)
        text_chunks_in_article_blocks.add(leftmost)
    msgn('!')
    return article_blocks

def clean_text(text):
    "replace nonprintable characters"
    r = ''
    for c in text:
        if ord(c)<32 or unicodedata.category(c)[0] not in 'LMNP':
            r += '_'
        else:
            r += c
    return r

VERSION='0'


if __name__=='__main__':
    parser = argparse.ArgumentParser(prog='pdfshapeminer',
            description='Extract text from pdf',
            formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    parser.add_argument('-v', dest='debuglevel', action='count',
                       default = 0,
                       help='Be verbose (repeat for more)')

    parser.add_argument('--draw-chunks', dest='draw_chunks', action='store_true',
                       help='Draw crude page representation, coloured chunks of text')

    parser.add_argument('--draw-blocks', dest='draw_blocks', action='store_true',
                       help='Draw crude page representation, coloured blocks (= short newspaper articles) of text')

    parser.add_argument('--hide-text', dest='hide_text', action='store_true',
                       help='Do not print the text. Useful with --draw-* and --print-stats.')


    parser.add_argument('--print-stats', dest='print_stats', action='store_true',
            help='Print statistics about blocks (suitable for importing into LibreOffice calc), tab separated entries of: STATS, nr_of_chunks, avg_chunk_width, stdev_of_chunk_width, avg_chunk_height, stdev_of_chunk_height, size_of_text_in_characters, first_20_chars_of_block')


    parser.add_argument('--line-height-diff', dest='line_height_diff', action='store',
                        default=0.1,
                        type=float,
                        help='Relative difference in line height where we consider the font to be different')

    parser.add_argument('--shear-limit', dest='shear_limit', action='store',
                        default=0.1,
                        type=float,
                        help='If the text is sheared above this limit, reject it')

    parser.add_argument('--rotation-limit', dest='rotation_limit', action='store',
                        default=2,
                        type=float,
                        help='If the text is rotated above this angle (in degrees), reject it')


    parser.add_argument('--max-line-spread', dest='max_line_spread', action='store',
                        default=1.2,
                        type=float,
                        help='Maximum height (multiply of line height) where we consider lines to belong to the same paragraph')

    parser.add_argument('--max-char-spread', dest='max_char_spread', action='store',
                        default=0.3,
                        type=float,
                        help='fraction of (vertical) line height to keep (horizontal) blocks apart; if the separation between consequitive blocks is lower, group them together')


    parser.add_argument('--version', action='version',
                       version='%(prog)s '+VERSION)

    parser.add_argument('pdffile', help='PDF file', default=None, nargs='?')
    parser.add_argument('args', nargs=argparse.REMAINDER)

    global options
    options, rest = parser.parse_known_args()
    assert not rest
    global debuglevel
    debuglevel = options.debuglevel


    DEBUG(3, options)
    pdffile = options.pdffile
    for page_chunks in get_text_chunks(pdffile):
        if options.draw_chunks:
            plotchunks(page_chunks)
        ablocks = get_article_blocks(page_chunks)
        if options.draw_blocks:
            plotblocks(ablocks)
        for ab in ablocks:
            ab.sort_chunks()
            abtext = ab.get_text()
            if options.print_stats:
                stats = ab.stats()
                nrchunks, avgwidth, stdevwidth, avgheight, stdevheight = stats
                text = clean_text(abtext)
                print('STATS',nrchunks, avgwidth, stdevwidth, avgheight, stdevheight, len(text), text[:20], sep='\t')
            if not options.hide_text:
                print(abtext)


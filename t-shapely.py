#!/usr/bin/python
# -*- coding: utf-8 -*-

import sys, re, unicodedata
from pprint import pprint

import random

from pdfminer.pdfdocument import PDFDocument, PDFNoOutlines
from pdfminer.pdfparser import PDFParser
from pdfminer.pdfinterp import PDFResourceManager, PDFPageInterpreter
from pdfminer.converter import PDFPageAggregator
from pdfminer.layout import LTPage, LTChar, LTAnno, LAParams, LTTextBox, LTTextLine
from pdfminer.pdfpage import PDFPage


from matplotlib import pyplot
import shapely.geometry
#from descartes.patch import PolygonPatch


class TBox:
    "box with a text, the basic building block of text page with layout"
    def __init__(self, x1, y1, x2, y2, text='', page_number=None):
        self.text = text
        self.page_number = page_number
        self.box = shapely.geometry.box(x1, y1, x2, y2)
        self.bounds = self.box.bounds
        self.exterior = self.box.exterior

    def union(self, other):
        assert self.page_number == other.page_number
        rtext = self.text+' '+other.text #FIXME test order by x
        rbox = self.box.union(other.box)
        x1, y1, x2, y2 = rbox.bounds
        rtbox = TBox(x1, y1, x2, y2, rtext, self.page_number)
        return rtbox

    def __repr__(self):
        x1, y1, x2, y2 = self.bounds
        text = self.text
        return u'TBox({x1}, {y1}, {x2}, {y2}, {text}'.format(**locals())

    __str__ = __repr__

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
            plot_coords(ax, tbox.exterior, color)
            xmin, ymin, xmax, ymax = tbox.bounds
            ax.text(xmin, ymin, tbox.text, fontsize=6)

            #patch = PolygonPatch(polygon, facecolor=v_color(True), edgecolor=v_color(True), alpha=0.5, zorder=2)
            #ax.add_patch(patch)


#    xrange = [0, 1000]
#    yrange = [0, 1000]
#    ax.set_xlim(*xrange)
#    ax.set_xticks(range(*xrange) + [xrange[-1]])
#    ax.set_ylim(*yrange)
#    ax.set_yticks(range(*yrange) + [yrange[-1]])
#    ax.set_aspect(1)

    pyplot.show()




import codecs
sys.stdout = codecs.getwriter('utf-8')(sys.stdout)

def msg(*s):
    r = ' '.join(str(x) for x in s)
    sys.stderr.write(r); sys.stderr.flush()

def msgn(*s):
    msg(*s)
    msg('\n')

def msgr(*s):
    msg(*s)
    msg('       \r')


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
                child_str = ''
                for child in item:
                    if isinstance(child, (LTChar, LTAnno)):
                        child_str += child.get_text()
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


fp = open(sys.argv[1], 'rb')
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

class TChunk:
    "keeps a list of TBox'es and a corresponding shapely object as their union"
    def __init__(self, tbox=None):
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
        lines = self.get_lines()
        textlines = (x.text for x in lines)
        text = '\n'.join(textlines) 
        text = fixlig(text)
        text = fixhyp(text)
        return text


    def __len__(self):
        return len(self.tboxes)

    def __repr__(self):
        return 'L:'+str(self.lineheight)+'; '.join(str(c) for c in self.tboxes)


# rozdiel vo vyskach riadkov (relativny), pri ktorych povazujeme font za rovnaky
line_height_diff = 0.1

# maximalny rozdiel vertikalnej pozicie (nasobky vysky riadku), pri ktorom povazujeme 
# riadky za patriace tomu istemu odseku
max_line_spread = 1.2

text_chunks = []

pagenumber = 0
for page in PDFPage.create_pages(doc):
    print '@@@ PG:', pagenumber
    if pagenumber == 5:
        break
    interpreter.process_page(page)
    # receive the LTPage object for this page
    pagenumber += 1


device.get_result()
for row in device.rows:
    text_chunks.append( TChunk(row) )

msgn('got results, chunks:', len(device.rows), len(text_chunks))

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
    print '@@@PG:', page,len(text_chunks)
    reduced = True
    while reduced:
        msgn('\n---')
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
                mls = (max_line_spread - 1) * (chunk1.lineheight + chunk2.lineheight) / 2
                mcs = 0.3*(chunk1.lineheight + chunk2.lineheight) / 2
                if (
                    (i!=j) and  
                    # riadky maju podobnu vysku
                    abs(chunk1.lineheight - chunk2.lineheight) / ((chunk1.lineheight + chunk2.lineheight)/2) < line_height_diff and
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


    for tc in text_chunks:
        print (tc.get_text())
        print '@@@'
    plotchunks(text_chunks)




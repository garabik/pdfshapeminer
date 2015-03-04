#!/usr/bin/python
# -*- coding: utf-8 -*-

import sys, re, unicodedata
from pprint import pprint

from pdfminer.pdfdocument import PDFDocument, PDFNoOutlines
from pdfminer.pdfparser import PDFParser
from pdfminer.pdfinterp import PDFResourceManager, PDFPageInterpreter
from pdfminer.converter import PDFPageAggregator
from pdfminer.layout import LTPage, LTChar, LTAnno, LAParams, LTTextBox, LTTextLine
from pdfminer.pdfpage import PDFPage


from matplotlib import pyplot
from shapely.geometry import box, MultiPolygon
from descartes.patch import PolygonPatch

SIZE = (10, 4)

def plot_coords(ax, ob):
    x, y = ob.xy
    ax.plot(x, y, 'o', color='#999999', zorder=1)

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
        u'ﬁ': 'fi'
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
#                    row = (page_number, item.bbox[0], item.bbox[1], item.bbox[2], item.bbox[3], child_str) # bbox == (x1, y1, x2, y2)
                    x1, y1, x2, y2 = item.bbox
                    row = page_number, box(x1, y1, x2, y2), child_str
                    self.rows.append(row)
                for child in item:
                    render(child, page_number)
            return
        render(ltpage, self.page_number)
        self.page_number += 1
        self.rows = sorted(self.rows, key = lambda x: x[0])
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

class TextBlock:
    ''' textblock sa sklada z chunkov

        chunk je: (polygon, text)
    '''
    def __init__(self, chunk=None):
        if chunk:
            self.chunks = [chunk]
            bounds = chunk[0].bounds
            self.bottom = bounds[1]
            self.left = self.mean_left = bounds[0]
            self.top = bounds[3]
            self.right = self.mean_right = bounds[2]
            self.height = self.lineheight = self.top - self.bottom
            assert self.height > 0
            assert self.bottom < self.top and self.left < self.right
        else:
            self.chunks = []
            self.bottom = self.top = self.left = self.right = self.height = self.lineheigh = 0

        # rows bude naplnene az po vytvoreni a zoskupeni vsetkych blokov, metodou create_rows
        self.rows = []

    def get_rows(self):
        rows = []
        # najprv roztriedime podla y-ovej suradnice
        chunks_by_y = {}
        for c in self.chunks:
            y1 = c[0].bounds[1]
            if y1 in chunks_by_y:
                chunks_by_y[y1].append(c)
            else:
                chunks_by_y[y1] = [c]
        # teraz zlucime chunky s podobnym y
        keys = sorted(chunks_by_y.keys(), reverse=True)
        i = 0
        while i < len(keys)-1:
            # ak sa y-nova suradnica lisi menej nez o iste percento vysky riadku, povazujeme to za jeden riadok
            if abs(keys[i] - keys[i+1]) / self.lineheight < 0.1: #FIXME parameter
                y1 = keys[i]
                y2 = keys[i+1] # y-ova suradnica druheho chunku
                chunks_by_y[y1].extend(chunks_by_y[y2])
                del chunks_by_y[y2]
                del keys[i+1]
            i += 1
        for k in keys:
            chunks = chunks_by_y[k] # all the chunks within one line
#            chunks_by_y[k].sort() # podla x-ovej suradnice
            chunks_by_y[k].sort(key=lambda x: x[0].bounds[0])
            # get bouding box of the line
            row = chunks[0][0]
            text = chunks[0][1]
            for i in range(1, len(chunks)):
                row = row.union(chunks[i][0])
                text += ' '+chunks[i][1]
            rows.append( (row, text) )
#            x1 = min(chunk[0] for chunk in chunks)
#            x2 = min(chunk[2] for chunk in chunks)
#            y1 = min(chunk[1] for chunk in chunks)
#            y2 = min(chunk[3] for chunk in chunks)
#            text = ' '.join(c[4] for c in chunks) 
#            rows.append( (x1, y1, x2, y2, text) )
        return rows

    def get_text_box(self):
        # text box is (box, text)
        rows = self.get_rows()
        x1 = min(row[0].bounds[0] for row in rows)
        x2 = min(row[0].bounds[2] for row in rows)
        y1 = min(row[0].bounds[1] for row in rows)
        y2 = min(row[0].bounds[3] for row in rows)
        text = '\n'.join(row[1] for row in rows) 
        text = fixlig(text)
        text = fixhyp(text)
        return box(x1, y1, x2, y2), text


    def append(self, chunk):
        self.chunks.append(chunk)
        g, t = chunk
        self.lineheight = sum(c[0].bounds[3]-c[0].bounds[1] for c in self.chunks)/len(self.chunks)
        self.height = max(c[0].bounds[3] for c in self.chunks) - min(c[0].bounds[1] for c in self.chunks)
        assert self.height > 0
        if g.bounds[0] < self.left:
            self.left = g.bounds[0]
        if g.bounds[2] > self.right:
            self.right = g.bounds[2]
        if g.bounds[1] < self.bottom:
            self.bottom = g.bounds[1]
        if g.bounds[3] > self.top:
            self.top = g.bounds[3]
        assert self.bottom < self.top and self.left < self.right
#        self.mean_left = sum(c[0] for c in self.chunks) / len(self)
#        self.mean_right = sum(c[2] for c in self.chunks) / len(self)
#        assert self.mean_left < self.mean_right

    def extend(self, chunks):
        for c in chunks:
            self.append(c)

    def __len__(self):
        return len(self.chunks)

    def __repr__(self):
        return 'L:'+str(self.lineheight)+'; '.join(str(c) for c in self.chunks)

    def __str__(self):
        return u'ML{ml:4.1f} MR{mr:4.1f} H{h:5.2f} B{bottom:5.1f} {r}'.format(ml=self.mean_left, mr=self.mean_right, h=self.lineheight, bottom=self.bottom, r='; '.join(c[1] for c in self.chunks))

# rozdiel vo vyskach riadkov (relativny), pri ktorych povazujeme font za rovnaky
line_height_diff = 0.1

# maximalny rozdiel vertikalnej pozicie (nasobky vysky riadku), pri ktorom povazujeme 
# riadky za patriace tomu istemu odseku
max_line_spread = 1.2


for page in PDFPage.create_pages(doc):
    interpreter.process_page(page)
    # receive the LTPage object for this page
    device.get_result()
    text_blocks = []
    for row in device.rows:
        page, polygon, text = row
        text_blocks.append( TextBlock( (polygon, text) ) )

    msgn('got results, chunks:', len(device.rows), len(text_blocks))


    reduced = True
    while reduced:
        msgn('\n---')
        reduced = False
        i = 0
        while i < len(text_blocks):
            block1 = text_blocks[i]
            j = i
            while j < len(text_blocks):
                msgr(i, j, len(text_blocks))
                block2 = text_blocks[j]
                # o kolko mozu byt bloky od seba v absolutnej hodnote, aby to este nebolo chapane ako prazdny riadok
                mls = (max_line_spread - 1) * (block1.lineheight + block2.lineheight) / 2
                if (
                    (i!=j) and  
                    # riadky maju podobnu vysku
                    abs(block1.lineheight - block2.lineheight) / ((block1.lineheight + block2.lineheight)/2) < line_height_diff and
                    # bloky sa vertikalne prekryvaju alebo su blizko k sebe
                    (
                        (block2.bottom-mls <= block1.bottom <= block2.top+mls) or (block1.bottom-mls <= block2.bottom <= block1.top+mls)
                    ) and
                    # bloky sa horizontalne prekryvaju
                    ( (block2.left <= block1.left <= block2.right) or (block1.left <= block2.left <= block1.right) )
                    ):
                    block1.extend(block2.chunks)
                    del text_blocks[j]
                    reduced = True
                else:
                    j += 1
            i += 1

#    pprint(text_blocks)
    for block in text_blocks:
#    print (block.__str__())
        print(block.get_text_box()[1])
        print '========'
    sys.exit()

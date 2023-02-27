BASE=https://jhc.sjtu.edu.cn/public/courses/CS2206/
MATERIALS=Intro BoolExprSem Syntax DenotationalSemantics
ASSIGNMENTS=0213 0216
ASSIGNMENT_PDFS=0220
ZIPS=SetsClass

%:
	wget "${BASE}$@"

all: pdfs sources assignment-sources assignment-pdfs zips

pdfs: $(foreach x,${MATERIALS},${x}.pdf)
sources: $(foreach x,${MATERIALS},${x}.v)
assignment-sources: $(foreach x,${ASSIGNMENTS},Assignment${x}.v)
assignment-pdfs: $(foreach x,${ASSIGNMENT_PDFS},Assignment${x}.pdf)
zips: $(foreach x,${ZIPS},${x}.zip)

.PHONY: all pdfs sources assignment-sources assignment-pdfs zips

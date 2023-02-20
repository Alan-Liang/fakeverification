BASE=https://jhc.sjtu.edu.cn/public/courses/CS2206/
MATERIALS=Intro BoolExprSem Syntax DenotationalSemantics
ASSIGNMENTS=0213 0216

%:
	wget "${BASE}$@"

all: pdfs sources assignment_sources

pdfs: $(foreach x,${MATERIALS},${x}.pdf)
sources: $(foreach x,${MATERIALS},${x}.v)
assignment_sources: $(foreach x,${ASSIGNMENTS},Assignment${x}.v)

.PHONY: all pdfs sources assignment_sources

.PHONY : all coq html install website clean

all: coq

html: coq
	$(MAKE) -C theories html

coq:
	$(MAKE) -C theories

install:
	$(MAKE) -C theories install

website: html
	test -d website || mkdir website
	cp theories/html/* website/
	cp extra/*.css extra/*.js website/

clean:
	$(MAKE) -C theories clean
	rm -rf website

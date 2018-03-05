.PHONY : all coq html website clean

all: coq

html: coq
	$(MAKE) -C theories html

coq:
	$(MAKE) -C theories

website: html
	test -d website || mkdir website
	cp theories/html/* website/
	cp extra/*.css extra/*.js website/

clean:
	$(MAKE) -C theories clean
	rm -rf website

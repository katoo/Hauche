hosh: hosh.scm
	gosh scm2exe -o hosh hosh.scm

install: hosh
	mv hosh /usr/local/bin

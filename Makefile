hosh: hosh.scm
	gosh scm2exe -o hosh hosh.scm

install: hosh
	install hosh /usr/local/bin

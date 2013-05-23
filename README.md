Haskell-like Offside Syntax and HTML template on Gauche

*INSTALL
$ git clone https://github.com/katoo/Hauche.git
$ cd Hauche
$ make
$ sudo make install

*Hello World
$ cat > hello.hos
#!/usr/local/bin/hosh
print "Hello World"
^D
$ hosh hello.hos
Hello World
$ chmod +x hello.hos
$ ./hello.hos
Hello World

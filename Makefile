DESTDIR ?= $(HOME)/bin
default: all

all: 
		@echo Building ask ...
		sbt assembly
		mkdir bin -p
		cp ask-app/target/scala-2.13/ask-app-*.jar bin/.
		cat ./contrib/exec_dummy bin/ask-app-*.jar > bin/ask
		chmod +x bin/ask

install:
		install -m 0755 -d $(DESTDIR)
		install -m 0755 bin/ask $(DESTDIR)

clean:
		rm -rf bin/
		rm -rf target/
		rm -rf ask-app/target/
		rm -rf ask-runtime/target/

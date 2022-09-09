
all: hata

meta:
	cd Program/MetaBuilder && stack install

hata: meta
	metabuild hata

run: hata
	./_build/bin/hata

justrun:
	./_build/bin/hata

clean: meta
	metabuild clean
	cd Program/MetaBuilder && stack clean


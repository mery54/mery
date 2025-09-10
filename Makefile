all:
	git add --all
	git commit -m "I commit"
	git push -u origin main


up:
	$(MAKE) -C /Users/mery/eventbfolder ht
	$(MAKE) -C /Users/mery/tlafolder ht	
	$(MAKE) -C /Users/mery/lectures/malg/webmovex ht   # cours malg et movex	
	$(MAKE) -C /Users/mery/github/teaching all
	$(MAKE) -C /Users/mery/webmery ht	


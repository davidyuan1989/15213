/*
*	Name: Fusheng Yuan
*	Andrew ID: fyuan
*/

#include <stdlib.h>
#include <getopt.h>
#include <unistd.h>
#include <stdio.h>
#include "cachelab.h" 

int numHits = 0, numMiss = 0, numEvic = 0;
int s = 0, b = 0, E = 0;
char *fileTrace = NULL;

typedef struct Line {
	int valid;
	int tag;
	struct Line *nextLine;  
}Line;

typedef struct Set {
	int maxLines;
	Line *lineHead;
	int curLines;
	struct Set *nextSet;
}Set;

void _delete(Set *set){
	numEvic++;
	Line *curLine = set -> lineHead;
	Line *preLine = NULL;

	while(curLine -> nextLine != NULL){
		preLine = curLine;
		curLine = curLine -> nextLine;
	}
	free(curLine);
	preLine -> nextLine = NULL;
}

void _append(int tag, Set *set){
	numMiss++;
	Line *newLine = (Line*)malloc(sizeof(Line));
	if(newLine == NULL){
		exit(1);
	}

	newLine -> tag = tag;
	newLine -> valid = 0;
	newLine -> nextLine = set -> lineHead;
	set -> lineHead = newLine;
	
	if(set -> curLines == set -> maxLines){
		_delete(set);
	}else{
		set -> curLines++;
	}
}

Set* _location(Set *set, unsigned int address){
	int indexSet = (address >> b) & ((1 << s) - 1 );

	if(indexSet > (1<<s))
		return NULL;
	while(--indexSet >= 0){
		set = set -> nextSet;
	}

	return set;
}

Set* construction(){
	int numSets = 1 << s;
	int maxLines = E;
	Set *headSet = (Set*)malloc(sizeof(Set));
	if(headSet == NULL){
		exit(1);
	}

	headSet -> maxLines = maxLines;
	headSet -> curLines = 0;
	Set *curSet = headSet;

	while(--numSets > 0){
		Set *set = (Set*)malloc(sizeof(Set));
		if(set == NULL){
			exit(1);
		}

		set -> maxLines = maxLines;
		set -> curLines = 0;
		set -> nextSet = NULL;
		set -> lineHead = NULL;
		curSet -> nextSet = set;
		curSet = set;
	}

	return headSet;
}

void search(Set *headSet, unsigned int address){
	int tag = address >> (b+s);
	Set *curSet = _location(headSet, address);
	if(curSet == NULL)
		return;
	Line *curLine = curSet -> lineHead;
	Line *preLine = NULL;

	while(curLine != NULL){
		if(curLine -> tag == tag){
			numHits++;
			if(preLine != NULL){
				preLine -> nextLine = curLine -> nextLine;
				curLine -> nextLine = curSet -> lineHead;
				curSet -> lineHead = curLine;
			}
			return;
		}
		preLine = curLine;
		curLine = curLine -> nextLine;
	}

	_append(tag, curSet);
}

void freeAll(Set *headSet){
	Set *curSet = headSet;
	
	while(curSet != NULL){
		Line *curLine = curSet -> lineHead;

		while(curLine != NULL){
			Line *tmpLine = curLine;
			curLine = curLine -> nextLine;
			free(tmpLine);
		}
		Set *tmpSet = curSet;
		curSet = curSet -> nextSet;
		free(tmpSet);
	}
}

void getOpts(int argc, char ** argv){
	int opt;

	while ((opt= getopt(argc, argv, "s:E:b:t:")) != -1) {
	    switch (opt){
		    case 's':
		      s = atoi(optarg);
		      break;
		    case 'E':
		      E = atoi(optarg);
		      break;
		    case 'b':
		      b = atoi(optarg);
		      break;
		    case 't':
		      fileTrace = optarg;
		      break;
		    default:
		        exit(EXIT_FAILURE);
	    }
  	}
}

int main(int argc, char ** argv){
	char ops;
	unsigned int address;
	int size;
	Set *headSet = NULL;
  	FILE *fp;

	getOpts(argc, argv);
	headSet = construction();
	fp = fopen(fileTrace, "r");

	/*read each line from log*/
	 while (fscanf(fp, " %c %x, %d\n", &ops, &address, &size) != EOF){
	 	if(ops == 'M'){
	 		search(headSet, address);
	 		numHits++;
	 	}else if(ops == 'L' || ops == 'S'){
	 		search(headSet, address);
	 	}
	 }

	 freeAll(headSet);
	 printSummary(numHits, numMiss, numEvic);
	 fclose(fp);
	 
	 return 0; 	
}

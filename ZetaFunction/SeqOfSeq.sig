175,0
S,ProcOnSeqElt,"Proc(~t, i, args), where t[i] eq s[I], considering I as multi-index",0,4,0,0,1,0,0,0,0,-1,,0,0,41,,0,0,82,,1,1,82,,-38,-38,-38,-38,-38,-38
S,AssignSeqElt,"s[I] := e, considering I as multi-index",0,3,0,0,1,0,0,0,0,-1,,0,0,82,,1,1,82,,-38,-38,-38,-38,-38,-38
S,AssignSeqElt,"s[I] := e, considering I as multi-index",0,4,0,0,1,0,0,0,0,-1,,0,0,82,,1,1,83,,1,1,82,,-38,-38,-38,-38,-38,-38
S,PlusAssignSeqElt,"s[I] +:= e, considering I as multi-index",0,3,0,0,1,0,0,0,0,-1,,0,0,82,,1,1,82,,-38,-38,-38,-38,-38,-38
S,PlusAssignSeqElt,"s[I] +:= e, considering I as multi-index",0,4,0,0,1,0,0,0,0,-1,,0,0,82,,1,1,83,,1,1,82,,-38,-38,-38,-38,-38,-38
S,TimesAssignSeqElt,"s[I] *:= e, considering I as multi-index",0,3,0,0,1,0,0,0,0,-1,,0,0,82,,1,1,82,,-38,-38,-38,-38,-38,-38
S,UndefineSeqElt,"Undefine S[I], considering I as multi-index",0,2,0,0,1,0,0,0,0,82,,1,1,82,,-38,-38,-38,-38,-38,-38
S,UndefineSeqElt,"Undefine S[I], considering I as multi-index",0,3,0,0,1,0,0,0,0,82,,1,1,83,,1,1,82,,-38,-38,-38,-38,-38,-38
S,SeqDepth,Count how many nested [...] has s (a sequence of sequences),0,1,0,0,0,0,0,0,0,82,,148,-38,-38,-38,-38,-38
S,FuncOnSeqElt,"Funct(t, i, args), where t[i] eq s[I], considering I as multi-index",0,4,0,0,0,0,0,0,0,-1,,0,0,41,,0,0,82,,0,0,82,,-1,-38,-38,-38,-38,-38
S,SeqElt,"Return s[I], considering I as multi-index",0,2,0,0,0,0,0,0,0,82,,0,0,82,,-1,-38,-38,-38,-38,-38
S,EvaluateSeq,"Evaluate each s[I] at xi=e, considering I as multi-index, for all I in indexs",0,4,0,0,1,0,0,0,0,-1,,0,0,469,,1,1,83,,1,1,82,,-38,-38,-38,-38,-38,-38
S,EvaluateSeq,"Evaluate each s[I] at xi=e, considering I as multi-index, for all I in indexs",0,4,0,0,1,0,0,0,0,-1,,0,0,148,,1,1,83,,1,1,82,,-38,-38,-38,-38,-38,-38
S,EvaluateSeq,"Evaluate each s[I] at xi=e, considering I as multi-index, for all I in indexs",0,4,0,0,0,0,0,0,0,-1,,0,0,469,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,EvaluateSeq,"Evaluate each s[I] at xi=e, considering I as multi-index, for all I in indexs",0,4,0,0,0,0,0,0,0,-1,,0,0,148,,0,0,83,,0,0,82,,82,83,-38,-38,-38,-38
S,PrintSeqD,"Print sequence of sequences s, element by element, listed by indexs, ordered by total sum of indexes, then the higher first indexs first, writing the indexes -1",0,2,0,0,1,0,0,0,0,83,,0,0,82,,-38,-38,-38,-38,-38,-38
S,PrintSeqFactors,"Print the factorization of each element of sequence of sequences s, listed by indexs, ordered by total sum of indexes, then the higher first indexs first, writing the indexes -1",0,2,0,0,1,0,0,0,0,83,,0,0,82,,-38,-38,-38,-38,-38,-38
S,PrintSeq,"Print sequence of sequences s, element by element, listed by indexs",0,2,0,0,1,0,0,0,0,83,,0,0,82,,-38,-38,-38,-38,-38,-38
S,+,Elementwise sum of the sequence (of sequences) s and the element e,0,2,0,0,0,0,0,0,0,-1,,0,0,82,,82,-38,-38,-38,-38,-38
S,+,Elementwise sum of the sequence (of sequences) s and the element e,0,2,0,0,0,0,0,0,0,82,,0,0,-1,,82,-38,-38,-38,-38,-38
S,+,"Elementwise sum of sequences (...of sequences) with zero removal, treating undef as 0 in element sums t1 : <s1, indexs1> t2 : <s2, indexs2>",0,2,0,0,0,0,0,0,0,303,,0,0,303,,82,83,-38,-38,-38,-38
S,-,Elementwise difference of the sequence (of sequences) s and the element e,0,2,0,0,0,0,0,0,0,-1,,0,0,82,,82,-38,-38,-38,-38,-38
S,*,"Elementwise product of the sequence (of sequences) s and another sequence, expanding the left sequence first, preserving undefined elements (=> preserving indexing)",0,2,0,0,0,0,0,0,0,82,,0,0,82,,82,-38,-38,-38,-38,-38
S,*,"Elementwise product of the sequence (of sequences) s and the element e, preserving undefined elements (=> preserving indexing)",0,2,0,0,0,0,0,0,0,-1,,0,0,82,,82,-38,-38,-38,-38,-38
S,*,"Elementwise product of the sequence (of sequences) s and the element e, preserving undefined elements (=> preserving indexing)",0,2,0,0,0,0,0,0,0,82,,0,0,-1,,82,-38,-38,-38,-38,-38
S,*,"Produt of sequences (...of sequences) t1 : <s1, indexs1> t2 : <s2, indexs2>",0,2,0,0,0,0,0,0,0,303,,0,0,303,,82,83,-38,-38,-38,-38
S,/,Elementwise quotient of the sequence (of sequences) s and the element e,0,2,0,0,0,0,0,0,0,-1,,0,0,82,,82,-38,-38,-38,-38,-38

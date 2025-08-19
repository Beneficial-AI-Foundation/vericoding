//ATOM
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}


//ATOM



predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}


//ATOM

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1],str2)
}


//ATOM
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..]))
}


//ATOM

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures res <==> isSubstringPred(sub, str)
	ensures res ==> isSubstringPred(sub, str)
	// ensures !res ==> !isSubstringPred(sub, str)
	ensures isSubstringPred(sub, str) ==> res
	ensures isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  res := false;
  assume res <==> isSubstringPred(sub, str);
  assume res ==> isSubstringPred(sub, str);
  assume isSubstringPred(sub, str) ==> res;
  assume isSubstringPred(sub, str) ==> res;
  assume !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.;
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  res := false;
  assume !res <==> isNotPrefixPred(pre,str);
  assume res <==> isPrefixPred(pre,str);
  return res;
}


//ATOM

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}


//ATOM

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}


//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;
	
	/* code modified by LLM (iteration 1): Fixed assignment to use existing parameter and added proper logic for k=0 case */
	if k == 0 {
		found := true;
		assert haveCommonKSubstringPred(k, str1, str2) by {
			assert 0 <= 0 <= |str1| - k;
			assert isSubstringPred(str1[0..0], str2) by {
				assert str1[0..0] == "";
				assert isPrefixPred("", str2[0..]) by {
					assert |""| <= |str2[0..]|;
					assert "" == str2[0..][..|""|];
				}
			}
		}
		return;
	}
	
	/* code modified by LLM (iteration 1): Added proper handling when str1 is too short */
	if |str1| < k {
		assert haveNotCommonKSubstringPred(k, str1, str2) by {
			forall i1, j1 | 0 <= i1 <= |str1|- k && j1 == i1 + k 
				ensures isNotSubstringPred(str1[i1..j1], str2)
			{
				assert i1 <= |str1| - k < 0;
				assert false;
			}
		}
		return;
	}
	
	var i := 0;
	/* code modified by LLM (iteration 1): Fixed loop invariants and bounds */
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		invariant forall i1 :: 0 <= i1 < i && i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2)
		decreases |str1| - k + 1 - i
	{
		var substring := str1[i..i+k];
		var isSubstr := isSubstring(substring, str2);
		
		if isSubstr {
			found := true;
			/* code modified by LLM (iteration 1): Added witness for existential quantifier */
			assert haveCommonKSubstringPred(k, str1, str2) by {
				assert 0 <= i <= |str1| - k;
				assert i + k == i + k;
				assert isSubstringPred(str1[i..i+k], str2);
			}
			return;
		}
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 1): Added proof that no common substring exists */
	assert haveNotCommonKSubstringPred(k, str1, str2) by {
		forall i1, j1 | 0 <= i1 <= |str1| - k && j1 == i1 + k 
			ensures isNotSubstringPred(str1[i1..j1], str2)
		{
			assert 0 <= i1 < i;
			assert isNotSubstringPred(str1[i1..i1+k], str2);
			assert str1[i1..j1] == str1[i1..i1+k];
		}
	}
}
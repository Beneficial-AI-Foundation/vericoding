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
	/* code modified by LLM (iteration 1): handle edge case where k=0 */
	if k == 0 {
		found := true;
		assert haveCommonKSubstringPred(k, str1, str2) by {
			if |str1| >= 0 {
				assert 0 <= 0 <= |str1| - 0;
				assert 0 == 0 + 0;
				assert str1[0..0] == "";
				assert isSubstringPred("", str2) by {
					assert 0 <= 0 <= |str2|;
					assert isPrefixPred("", str2[0..]) by {
						assert |""| <= |str2[0..]|;
						assert "" == str2[0..][..|""|];
					}
				}
			}
		}
		return;
	}
	
	/* code modified by LLM (iteration 1): handle edge case where string is too short */
	if |str1| < k {
		found := false;
		assert haveNotCommonKSubstringPred(k, str1, str2) by {
			forall i1, j1 | 0 <= i1 <= |str1| - k && j1 == i1 + k
				ensures isNotSubstringPred(str1[i1..j1], str2)
			{
				assert |str1| - k < 0;
				assert !(0 <= i1 <= |str1| - k);
			}
		}
		return;
	}
	
	found := false;
	var i := 0;
	
	/* code modified by LLM (iteration 1): improved loop with proper invariants */
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		invariant !found
		invariant forall i1 :: 0 <= i1 < i && i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2)
	{
		var substring := str1[i..i+k];
		var isSubstr := isSubstring(substring, str2);
		
		if isSubstr {
			found := true;
			/* code modified by LLM (iteration 1): assertion to establish postcondition */
			assert haveCommonKSubstringPred(k, str1, str2) by {
				assert 0 <= i <= |str1| - k;
				assert i + k == i + k;
				assert isSubstringPred(str1[i..i+k], str2);
			}
			return;
		}
		
		/* code modified by LLM (iteration 1): assertion to maintain loop invariant */
		assert isNotSubstringPred(str1[i..i+k], str2);
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 1): final assertion when no substring found */
	assert haveNotCommonKSubstringPred(k, str1, str2) by {
		forall i1, j1 | 0 <= i1 <= |str1| - k && j1 == i1 + k
			ensures isNotSubstringPred(str1[i1..j1], str2)
		{
			assert j1 == i1 + k;
			assert str1[i1..j1] == str1[i1..i1+k];
			assert 0 <= i1 <= |str1| - k;
			assert i1 < i;
			assert isNotSubstringPred(str1[i1..i1+k], str2);
		}
	}
}
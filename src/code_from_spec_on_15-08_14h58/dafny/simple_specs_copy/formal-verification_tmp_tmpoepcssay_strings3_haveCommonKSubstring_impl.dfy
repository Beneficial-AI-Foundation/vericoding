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
  assume !res <==> isNotSubstringPred(sub, str); // This postcondition follows from the above lemma.
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


//IMPL 

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;
	
	if k == 0 {
		/* code modified by LLM (iteration 1): handle k=0 case properly */
		found := true;
		// When k=0, empty substring exists in any string
		assert str1[0..0] == "";
		assert isPrefixPred("", str2);
		assert isSubstringPred("", str2);
		assert haveCommonKSubstringPred(k, str1, str2);
		return;
	}
	
	if |str1| < k {
		/* code modified by LLM (iteration 1): handle insufficient length case */
		found := false;
		// When str1 is too short, no k-length substring exists
		assert forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==> false;
		assert haveNotCommonKSubstringPred(k, str1, str2);
		return;
	}
	
	var i := 0;
	/* code modified by LLM (iteration 1): fixed loop with proper invariants and triggers */
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		invariant !found ==> forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2) by {
			forall i1 | 0 <= i1 < i ensures isNotSubstringPred(str1[i1..i1+k], str2) {}
		}
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	{
		var substring := str1[i..i+k];
		var isCommon := isSubstring(substring, str2);
		
		if isCommon {
			found := true;
			/* code modified by LLM (iteration 1): added assertions to establish postcondition */
			assert isSubstringPred(substring, str2);
			assert substring == str1[i..i+k];
			assert i + k <= |str1|;
			assert 0 <= i <= |str1| - k;
			assert haveCommonKSubstringPred(k, str1, str2) by {
				assert exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2);
			}
			return;
		} else {
			/* code modified by LLM (iteration 1): establish loop invariant maintenance */
			assert isNotSubstringPred(substring, str2);
			assert substring == str1[i..i+k];
		}
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 1): establish final postcondition with proper quantifier handling */
	assert i == |str1| - k + 1;
	assert forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2) by {
		forall i1 | 0 <= i1 < i ensures isNotSubstringPred(str1[i1..i1+k], str2) {}
	}
	assert forall i1 :: 0 <= i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2) by {
		forall i1 | 0 <= i1 <= |str1| - k ensures isNotSubstringPred(str1[i1..i1+k], str2) {
			assert i1 < i;
		}
	}
	assert haveNotCommonKSubstringPred(k, str1, str2) by {
		forall i1, j1 | 0 <= i1 <= |str1|- k && j1 == i1 + k ensures isNotSubstringPred(str1[i1..j1],str2) {
			assert isNotSubstringPred(str1[i1..i1+k], str2);
			assert str1[i1..j1] == str1[i1..i1+k];
		}
	}
}
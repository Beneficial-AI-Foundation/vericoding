//IMPL FindAllOccurrences
method FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
	ensures forall i :: i in offsets ==> i + |pattern| <= |text|
	ensures forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
{
    offsets := {};
    var i:int := 0;
	// no pattern in text at all.
    if |pattern| > |text|
    {
        return offsets;
    }

	/* code modified by LLM (iteration 4): Fixed empty pattern case to handle all valid positions correctly */
    if pattern == ""
    {
        while i <= |text|
            invariant 0 <= i <= |text| + 1
            invariant offsets == set j | 0 <= j < i
            invariant forall j :: j in offsets ==> j + |pattern| <= |text|
		{
			offsets := offsets + {i};
            i:=i+1;
		}
		return offsets;
    }

    var pattern_hash: int := RecursiveSumDown(pattern);
    var text_hash: int := RecursiveSumDown(text[..|pattern|]);
    
	if pattern_hash == text_hash{
        if text[..|pattern|] == pattern
        {
            offsets := offsets + {0};
        }
    }
	else
	{
        LemmaRabinKarp(text[..|pattern|], pattern, text_hash, pattern_hash);
    }

    /* code modified by LLM (iteration 4): Fixed loop condition to include all positions and corrected invariants */
	while i < |text| - |pattern|
        invariant 0 <= i <= |text| - |pattern|
        invariant pattern_hash == RecursiveSumDown(pattern)
        invariant text_hash == RecursiveSumDown(text[i..i+|pattern|])
        invariant forall j :: j in offsets ==> j + |pattern| <= |text|
        invariant forall j :: 0 <= j <= i && j + |pattern| <= |text| ==> (text[j..j+|pattern|] == pattern <==> j in offsets)
	{
		//updating text hash
		var old_text_hash := text_hash;
		var left_letter_as_int := text[i] as int;
		var right_new_letter_as_int := text[i+|pattern|] as int;
		text_hash := text_hash - left_letter_as_int + right_new_letter_as_int;
		//updating i
		i := i + 1;
		
		/* code modified by LLM (iteration 4): Ensure hash invariant is maintained */
		LemmaHashEqualty(text_hash, text, i, old_text_hash, pattern);
		
		//checking hash equality
		if pattern_hash == text_hash{
			if text[i..i + |pattern|] == pattern
			{
				offsets := offsets + {i};
			}
		}
		else{
			LemmaRabinKarp(text[i..i+|pattern|], pattern, text_hash, pattern_hash);
		}
		
		/* code modified by LLM (iteration 4): Apply lemma to maintain biconditional invariant */
		Lemma2Sides(text, pattern, i, offsets);
	}
    
    /* code modified by LLM (iteration 4): Removed redundant post-loop handling since invariant ensures correctness */
}

//ATOM RecursiveSumDown
function RecursiveSumDown(str: string): int
{
	if str == "" then 0 else str[|str|-1] as int +RecursiveSumDown(str[..|str|-1])
}

//ATOM RecursiveSumUp
function RecursiveSumUp(str: string): int
{
	if str == "" then 0 else str[0] as int + RecursiveSumUp(str[1..])
}

//ATOM LemmaRabinKarp
lemma LemmaRabinKarp(t_sub:string, pattern:string, text_hash:int, pattern_hash:int)
    requires text_hash != pattern_hash
    requires pattern_hash == RecursiveSumDown(pattern)
    requires text_hash == RecursiveSumDown(t_sub)
    ensures t_sub[..] != pattern[..]
{}

//ATOM Lemma2Sides
lemma Lemma2Sides(text: string, pattern: string, i: nat, offsets: set<nat>)
	requires 0 <= i <= |text| - |pattern|
	requires (text[i..i+|pattern|] == pattern ==> i in offsets)
	requires (text[i..i+|pattern|] == pattern <== i in offsets)
	ensures (text[i..i+|pattern|] == pattern <==> i in offsets)
{}

//ATOM LemmaHashEqualty
lemma LemmaHashEqualty(text_hash : int, text: string, i: nat, old_text_hash: int, pattern: string)
requires 0 < i <= |text| - |pattern|
requires text_hash == old_text_hash - text[i - 1] as int + text[i - 1 + |pattern|] as int
requires  old_text_hash == RecursiveSumDown(text[i - 1..i - 1 + |pattern|]);
ensures text_hash == RecursiveSumDown(text[i..i+|pattern|])
{
	ghost var temp_val := old_text_hash + text[i - 1 + |pattern|] as int;
	ghost var str := text[i - 1..];
	LemmaAddingOneIndex(str, |pattern|, old_text_hash);
	PrependSumUp(text[i - 1..i + |pattern|]);
	EquivalentSumDefinitions(text[i - 1..i + |pattern|]);
	EquivalentSumDefinitions(text[i..i + |pattern|]);
}

//ATOM LemmaAddingOneIndex
lemma LemmaAddingOneIndex(str: string, i: nat, sum: int)
	requires 0 <= i < |str| && sum == RecursiveSumDown(str[..i])
	ensures 0 <= i+1 <= |str| && sum + str[i] as int == RecursiveSumDown(str[..i+1])
{
	var str1 := str[..i+1];
	calc {
		RecursiveSumDown(str[..i+1]);
	== // def.
		if str1 == [] then 0 else str1[|str1|-1] as int + RecursiveSumDown(str1[..|str1|-1]);
	== { assert str1 != []; } // simplification for a non-empty sequence
		str1[|str1|-1] as int + RecursiveSumDown(str1[..|str1|-1]);
	== { assert |str1|-1 == i; }
		str1[i] as int + RecursiveSumDown(str1[..i]);
	== { assert str1[..i] == str[..i]; }
		str[i] as int + RecursiveSumDown(str[..i]);
	== // inv.
		str[i] as int + sum;
	==
		sum + str[i] as int;
	}
}

//ATOM PrependSumUp
lemma PrependSumUp(str: string)
	requires str != ""
	ensures RecursiveSumUp(str) == str[0] as int + RecursiveSumUp(str[1..])
{
	// directly from the definition of RecursiveSumUp (for a non-emty sequence)
}

//ATOM EquivalentSumDefinitions
lemma EquivalentSumDefinitions(str: string)
	ensures RecursiveSumDown(str) == RecursiveSumUp(str)
{
	if |str| == 0
	{
	}
	else if |str| == 1
	{
	}
	else
	{
		var first: char, mid: string, last:char := str[0], str[1..|str|-1], str[|str|-1];
		calc {
			RecursiveSumDown(str);
		== { assert str != [] && str[|str|-1] == last && str[..|str|-1] == [first] + mid; }
			last as int + RecursiveSumDown([first] + mid);
		== // arithmetic
			RecursiveSumDown([first] + mid) + last as int;
		== { EquivalentSumDefinitions([first] + mid); } // induction hypothesis
			RecursiveSumUp([first] + mid) + last as int;
		== { assert [first] + mid != []; }
			first as int + RecursiveSumUp(mid) + last as int;
		== { EquivalentSumDefinitions(mid); } // induction hypothesis
			first as int + RecursiveSumDown(mid) + last as int;
		==
			first as int + RecursiveSumDown(mid + [last]);
		== { EquivalentSumDefinitions(mid + [last]); } // induction hypothesis
			first as int + RecursiveSumUp(mid + [last]);
		== { assert str != [] && str[0] == first && str[1..] == mid + [last]; }
			RecursiveSumUp(str);
		}
	}
}
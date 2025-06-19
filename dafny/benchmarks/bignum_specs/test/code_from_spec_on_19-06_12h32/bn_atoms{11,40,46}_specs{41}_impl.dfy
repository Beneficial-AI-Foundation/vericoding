// ATOMS
// BN_11
predicate ValidBitString(s: string) 
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// BN_46
function Exp_int(x: nat, y:nat): nat 
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

// BN_40
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//IMPL
lemma Str2IntLemma(s: string, i: nat)
requires ValidBitString(s)
requires 0 <= i <= |s|-1
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{
  /* code modified by LLM (iteration 1): Fixed proof using proper induction on suffix length */
  var prefix := s[..i+1];
  var suffix := s[i+1..];
  var k := |s| - 1 - i; // length of suffix
  
  if k == 0 {
    // Base case: suffix is empty
    assert suffix == "";
    assert Str2Int(suffix) == 0;
    assert Exp_int(2, 0) == 1;
    assert prefix == s;
    assert Str2Int(s) == Str2Int(prefix) * 1 + 0;
  } else {
    // Inductive case: prove by induction on the structure
    Str2IntLemmaHelper(s, i);
  }
}

/* code modified by LLM (iteration 1): Fixed helper lemma name and implementation */
lemma Str2IntLemmaHelper(s: string, i: nat)
requires ValidBitString(s)
requires 0 <= i <= |s|-2
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
decreases |s| - 1 - i
{
  var prefix := s[..i+1];
  var suffix := s[i+1..];
  var k := |s| - 1 - i;
  
  if k == 1 {
    // Base case: suffix has length 1
    assert |suffix| == 1;
    assert suffix == s[i+1..i+2];
    assert suffix[0] == s[i+1];
    assert s[i+1] == s[|s|-1]; // since k == 1 means i+1 == |s|-1
    
    // From Str2Int definition
    calc {
      Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == 2 * Str2Int(s[..i+1]) + (if s[|s|-1] == '1' then 1 else 0);
      == 2 * Str2Int(prefix) + (if s[i+1] == '1' then 1 else 0);
      == Str2Int(prefix) * Exp_int(2, 1) + Str2Int(suffix);
      == Str2Int(prefix) * Exp_int(2, k) + Str2Int(suffix);
    }
  } else {
    // Inductive case: k > 1
    assert i + 1 <= |s| - 2;
    Str2IntLemmaHelper(s, i + 1);
    
    // This gives us: Str2Int(s) == Str2Int(s[..i+2]) * Exp_int(2, k-1) + Str2Int(s[i+2..])
    var mid_prefix := s[..i+2];
    var tail := s[i+2..];
    
    assert Str2Int(s) == Str2Int(mid_prefix) * Exp_int(2, k-1) + Str2Int(tail);
    
    // Express mid_prefix in terms of prefix and next character
    assert mid_prefix == prefix + s[i+1..i+2];
    assert ValidBitString(mid_prefix);
    assert Str2Int(mid_prefix) == 2 * Str2Int(prefix) + (if s[i+1] == '1' then 1 else 0);
    
    // Express suffix in terms of its first character and tail  
    assert suffix == s[i+1..i+2] + tail;
    assert ValidBitString(suffix);
    
    // Use the recursive structure of Str2Int on suffix
    calc {
      Str2Int(suffix);
      == 2 * Str2Int(suffix[0..|suffix|-1]) + (if suffix[|suffix|-1] == '1' then 1 else 0);
      == 2 * Str2Int(s[i+1..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      == 2 * Str2Int(tail) + (if s[|s|-1] == '1' then 1 else 0);
    }
    
    // Now prove the main equation using algebra
    calc {
      Str2Int(s);
      == Str2Int(mid_prefix) * Exp_int(2, k-1) + Str2Int(tail);
      == (2 * Str2Int(prefix) + (if s[i+1] == '1' then 1 else 0)) * Exp_int(2, k-1) + Str2Int(tail);
      == 2 * Str2Int(prefix) * Exp_int(2, k-1) + (if s[i+1] == '1' then 1 else 0) * Exp_int(2, k-1) + Str2Int(tail);
      == Str2Int(prefix) * (2 * Exp_int(2, k-1)) + (if s[i+1] == '1' then 1 else 0) * Exp_int(2, k-1) + Str2Int(tail);
      == Str2Int(prefix) * Exp_int(2, k) + (if s[i+1] == '1' then 1 else 0) * Exp_int(2, k-1) + Str2Int(tail);
    }
    
    // Show that the last two terms equal Str2Int(suffix)
    assert (if s[i+1] == '1' then 1 else 0) * Exp_int(2, k-1) + Str2Int(tail) == 
           (if s[i+1] == '1' then 1 else 0) * Exp_int(2, k-1) + 2 * Str2Int(tail) + (if s[|s|-1] == '1' then 1 else 0) - 2 * Str2Int(tail);
    
    // This should equal Str2Int(suffix) by the calculation above
    assert Str2Int(suffix) == 2 * Str2Int(tail) + (if s[|s|-1] == '1' then 1 else 0);
    assert (if s[i+1] == '1' then 1 else 0) * Exp_int(2, k-1) + Str2Int(tail) + 2 * Str2Int(tail) + (if s[|s|-1] == '1' then 1 else 0) - 2 * Str2Int(tail) == 
           (if s[i+1] == '1' then 1 else 0) * Exp_int(2, k-1) + Str2Int(tail) + Str2Int(suffix) - 2 * Str2Int(tail);
    
    /* code modified by LLM (iteration 1): Simplified final step */
    // The key insight: we need to show the recursive relationship holds
    assert Str2Int(s) == Str2Int(prefix) * Exp_int(2, k) + Str2Int(suffix);
  }
}
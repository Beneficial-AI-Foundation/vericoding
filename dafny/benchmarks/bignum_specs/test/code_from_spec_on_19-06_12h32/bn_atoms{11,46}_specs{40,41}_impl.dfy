// ATOM
predicate ValidBitString(s: string) // BN_11
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM
function Exp_int(x: nat, y:nat): nat // BN_46
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

//IMPL
function Str2Int(s: string): nat 
  requires ValidBitString(s)
{
  if |s| == 0 then 0
  else (if s[0] == '1' then 1 else 0) * Exp_int(2, |s|-1) + Str2Int(s[1..])
}

//IMPL
lemma Str2IntLemma(s: string, i: nat)
requires ValidBitString(s)
requires 0 <= i <= |s|-1
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{
  /* code modified by LLM (iteration 1): Fixed proof by induction on string length with proper base and inductive cases */
  if |s| == 1 {
    // Base case: when s has length 1, i must be 0
    assert i == 0;
    assert s[..1] == s;
    assert s[1..] == "";
    assert Str2Int(s[1..]) == 0;
    assert Exp_int(2, 0) == 1;
    // Both sides equal Str2Int(s)
  } else {
    // Inductive case: prove by induction on the structure
    /* code modified by LLM (iteration 1): Added proper inductive proof structure */
    if i == 0 {
      // When i == 0: s[..1] is just [s[0]], s[1..] is the tail
      assert s[..1][0] == s[0];
      assert |s[..1]| == 1;
      assert Str2Int(s[..1]) == (if s[0] == '1' then 1 else 0);
      assert Exp_int(2, |s|-1 - 0) == Exp_int(2, |s|-1);
      // LHS: Str2Int(s) = (s[0] bit value) * Exp_int(2, |s|-1) + Str2Int(s[1..])
      // RHS: (s[0] bit value) * Exp_int(2, |s|-1) + Str2Int(s[1..])
    } else {
      // When i > 0: use induction on the tail s[1..]
      var tail := s[1..];
      assert ValidBitString(tail);
      assert 0 <= i-1 <= |tail|-1;
      
      /* code modified by LLM (iteration 1): Apply inductive hypothesis on tail with adjusted index */
      Str2IntLemma(tail, i-1);
      
      // From IH: Str2Int(tail) == Str2Int(tail[..i]) * Exp_int(2, |tail|-1-(i-1)) + Str2Int(tail[i..])
      assert Str2Int(tail) == Str2Int(tail[..i]) * Exp_int(2, |tail|-i) + Str2Int(tail[i..]);
      
      /* code modified by LLM (iteration 1): Establish key string slice relationships */
      assert tail[..i] == s[1..i+1];
      assert tail[i..] == s[i+1..];
      assert |tail| == |s| - 1;
      
      // Therefore: Str2Int(s[1..]) == Str2Int(s[1..i+1]) * Exp_int(2, |s|-1-i) + Str2Int(s[i+1..])
      
      /* code modified by LLM (iteration 1): Connect the full string to the decomposition */
      // We need to show: Str2Int(s[..i+1]) * Exp_int(2, |s|-1-i) + Str2Int(s[i+1..])
      // Note that s[..i+1] = [s[0]] + s[1..i+1]
      
      // Key insight: Str2Int(s[..i+1]) can be computed as:
      // (s[0] bit value) * Exp_int(2, i) + Str2Int(s[1..i+1])
      
      var s0_val := if s[0] == '1' then 1 else 0;
      assert Str2Int(s[..i+1]) == s0_val * Exp_int(2, i) + Str2Int(s[1..i+1]);
      
      /* code modified by LLM (iteration 1): Use exponential arithmetic to complete the proof */
      // Multiply by Exp_int(2, |s|-1-i):
      // Str2Int(s[..i+1]) * Exp_int(2, |s|-1-i) = 
      // (s0_val * Exp_int(2, i) + Str2Int(s[1..i+1])) * Exp_int(2, |s|-1-i)
      // = s0_val * Exp_int(2, i) * Exp_int(2, |s|-1-i) + Str2Int(s[1..i+1]) * Exp_int(2, |s|-1-i)
      // = s0_val * Exp_int(2, |s|-1) + Str2Int(s[1..i+1]) * Exp_int(2, |s|-1-i)
      
      ExpMultiplicative(2, i, |s|-1-i);
      assert Exp_int(2, i) * Exp_int(2, |s|-1-i) == Exp_int(2, i + (|s|-1-i)) == Exp_int(2, |s|-1);
      
      // So: Str2Int(s[..i+1]) * Exp_int(2, |s|-1-i) + Str2Int(s[i+1..])
      // = s0_val * Exp_int(2, |s|-1) + Str2Int(s[1..i+1]) * Exp_int(2, |s|-1-i) + Str2Int(s[i+1..])
      // = s0_val * Exp_int(2, |s|-1) + (Str2Int(s[1..]) from IH)
      // = s0_val * Exp_int(2, |s|-1) + Str2Int(s[1..])
      // = Str2Int(s)
    }
  }
}

/* code modified by LLM (iteration 1): Added helper lemma for exponential arithmetic */
lemma ExpMultiplicative(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a) * Exp_int(x, b) == Exp_int(x, a + b)
{
  if a == 0 {
    assert Exp_int(x, a) == 1;
    assert Exp_int(x, a + b) == Exp_int(x, b);
  } else {
    ExpMultiplicative(x, a-1, b);
    assert Exp_int(x, a-1) * Exp_int(x, b) == Exp_int(x, a-1 + b);
    assert Exp_int(x, a) == x * Exp_int(x, a-1);
    assert Exp_int(x, a + b) == x * Exp_int(x, a-1 + b);
  }
}
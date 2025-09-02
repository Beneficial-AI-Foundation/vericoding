//ATOM Steps
datatype Steps = One | Two

//IMPL climbStairs
method climbStairs(n: nat) returns (count: nat) 
  ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
  if n == 0 {
    var ss := {[]};
    count := 1;
    /* code modified by LLM (iteration 4): added explicit assertion with witness set */
    assert allEndAtN(ss, n);
    return;
  }
  
  if n == 1 {
    var ss := {[One]};
    count := 1;
    /* code modified by LLM (iteration 4): added explicit assertion with witness set */
    assert allEndAtN(ss, n);
    return;
  }
  
  // Use dynamic programming approach
  var prev2 := 1; // ways to reach step 0
  var prev1 := 1; // ways to reach step 1
  var current := 0;
  
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant prev2 == countWaysToClimb(i - 2)
    invariant prev1 == countWaysToClimb(i - 1)
  {
    current := prev1 + prev2;
    /* code modified by LLM (iteration 4): added lemma call to maintain counting property */
    countWaysProperty(i);
    prev2 := prev1;
    prev1 := current;
    i := i + 1;
  }
  
  count := current;
  
  /* code modified by LLM (iteration 4): establish the witness set exists */
  var ss := allValidSequences(n);
  countCorrectnessLemma(n);
  assert count == countWaysToClimb(n);
  assert |ss| == countWaysToClimb(n);
  assert count == |ss| && allEndAtN(ss, n);
}

predicate allEndAtN(ss: set<seq<Steps>>, n: nat)
{
  forall s :: s in ss ==> sumSteps(s) == n
}

function sumSteps(s: seq<Steps>): nat
  /* code modified by LLM (iteration 4): added decreases clause for termination */
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == One then 1 else 2) + sumSteps(s[1..])
}

/* code modified by LLM (iteration 4): defined countWaysToClimb function */
function countWaysToClimb(n: nat): nat
  decreases n
{
  if n == 0 then 1
  else if n == 1 then 1
  else countWaysToClimb(n-1) + countWaysToClimb(n-2)
}

/* code modified by LLM (iteration 4): defined function to get all valid sequences with proper construction */
function allValidSequences(n: nat): set<seq<Steps>>
  ensures allEndAtN(allValidSequences(n), n)
  decreases n
{
  if n == 0 then {[]}
  else if n == 1 then {[One]}
  else 
    (set s | s in allValidSequences(n-1) :: [One] + s) +
    (set s | s in allValidSequences(n-2) :: [Two] + s)
}

/* code modified by LLM (iteration 4): helper lemma to establish counting property */
lemma countWaysProperty(i: nat)
  requires i >= 2
  ensures countWaysToClimb(i) == countWaysToClimb(i-1) + countWaysToClimb(i-2)
{
  // This follows directly from the definition of countWaysToClimb
}

/* code modified by LLM (iteration 4): main correctness lemma with proper structure */
lemma countCorrectnessLemma(n: nat)
  ensures |allValidSequences(n)| == countWaysToClimb(n)
  decreases n
{  
  if n == 0 {
    /* code modified by LLM (iteration 4): base case proof */
    assert allValidSequences(0) == {[]};
    assert |allValidSequences(0)| == 1;
    assert countWaysToClimb(0) == 1;
  } else if n == 1 {
    /* code modified by LLM (iteration 4): base case proof */
    assert allValidSequences(1) == {[One]};
    assert |allValidSequences(1)| == 1;
    assert countWaysToClimb(1) == 1;
  } else {
    /* code modified by LLM (iteration 4): inductive case */
    countCorrectnessLemma(n-1);
    countCorrectnessLemma(n-2);
    
    var seqsFromN1 := set s | s in allValidSequences(n-1) :: [One] + s;
    var seqsFromN2 := set s | s in allValidSequences(n-2) :: [Two] + s;
    
    /* code modified by LLM (iteration 4): establish disjointness */
    forall s1, s2 | s1 in seqsFromN1 && s2 in seqsFromN2
      ensures s1 != s2
    {
      assert |s1| > 0 && s1[0] == One;
      assert |s2| > 0 && s2[0] == Two;
      assert One != Two;
    }
    
    /* code modified by LLM (iteration 4): use set cardinality properties */
    assert seqsFromN1 * seqsFromN2 == {};
    assert |seqsFromN1 + seqsFromN2| == |seqsFromN1| + |seqsFromN2|;
    assert |seqsFromN1| == |allValidSequences(n-1)|;
    assert |seqsFromN2| == |allValidSequences(n-2)|;
    assert allValidSequences(n) == seqsFromN1 + seqsFromN2;
  }
}
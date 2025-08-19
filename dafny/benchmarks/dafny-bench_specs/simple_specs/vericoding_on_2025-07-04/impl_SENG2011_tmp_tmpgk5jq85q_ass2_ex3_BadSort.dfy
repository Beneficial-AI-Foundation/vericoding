//ATOM
// verifies
// all bs are before all as which are before all ds
predicate sortedbad(s:string) 
{
  // all b's are before all a's and d's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j &&
  // all a's are after all b's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j &&
  // all a's are before all d's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j &&
  // all d's are after a;; b's and a's
  forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j
}

//IMPL BadSort
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
ensures sortedbad(b)
ensures multiset(a[..]) == multiset(b[..])
ensures |a| == |b|
{
    var countB := 0;
    var countA := 0;
    var countD := 0;
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant countB + countA + countD == i
        /* code modified by LLM (iteration 3): Fixed multiset counting using helper function */
        invariant countB == CountChar(a[..i], 'b')
        invariant countA == CountChar(a[..i], 'a')
        invariant countD == CountChar(a[..i], 'd')
    {
        if a[i] == 'b' {
            countB := countB + 1;
        } else if a[i] == 'a' {
            countA := countA + 1;
        } else {
            countD := countD + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 3): Fixed multiset syntax in assertions */
    assert countB == CountChar(a[..], 'b');
    assert countA == CountChar(a[..], 'a');
    assert countD == CountChar(a[..], 'd');
    
    b := "";
    var j := 0;
    while j < countB
        invariant 0 <= j <= countB
        invariant |b| == j
        invariant forall k :: 0 <= k < j ==> b[k] == 'b'
    {
        b := b + "b";
        j := j + 1;
    }
    
    /* code modified by LLM (iteration 3): Added assertion about b structure after first loop */
    assert |b| == countB;
    assert forall k :: 0 <= k < countB ==> b[k] == 'b';
    
    j := 0;
    while j < countA
        invariant 0 <= j <= countA
        invariant |b| == countB + j
        invariant forall k :: 0 <= k < countB ==> b[k] == 'b'
        invariant forall k :: countB <= k < countB + j ==> b[k] == 'a'
    {
        b := b + "a";
        j := j + 1;
    }
    
    /* code modified by LLM (iteration 3): Added assertion about b structure after second loop */
    assert |b| == countB + countA;
    assert forall k :: 0 <= k < countB ==> b[k] == 'b';
    assert forall k :: countB <= k < countB + countA ==> b[k] == 'a';
    
    j := 0;
    while j < countD
        invariant 0 <= j <= countD
        invariant |b| == countB + countA + j
        invariant forall k :: 0 <= k < countB ==> b[k] == 'b'
        invariant forall k :: countB <= k < countB + countA ==> b[k] == 'a'
        invariant forall k :: countB + countA <= k < countB + countA + j ==> b[k] == 'd'
    {
        b := b + "d";
        j := j + 1;
    }
    
    /* code modified by LLM (iteration 3): Added final structural assertions */
    assert |b| == countB + countA + countD;
    assert |b| == |a|;
    assert forall k :: 0 <= k < countB ==> b[k] == 'b';
    assert forall k :: countB <= k < countB + countA ==> b[k] == 'a';
    assert forall k :: countB + countA <= k < |b| ==> b[k] == 'd';
    
    /* code modified by LLM (iteration 3): Added lemma call to establish multiset equality */
    MultisetEqualityLemma(a, b, countB, countA, countD);
    
    /* code modified by LLM (iteration 3): Explicit assertion for sortedbad conditions */
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd') ==> i < j;
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'b' ==> i > j;
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'a' && b[j] == 'd' ==> i < j;
    assert forall i,j :: 0 <= i < |b| && 0 <= j < |b| && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b') ==> i > j;
    assert sortedbad(b);
}

/* code modified by LLM (iteration 3): Added helper function to count characters */
function CountChar(s: string, c: char): nat
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

/* code modified by LLM (iteration 3): Added helper lemma to establish multiset equality */
lemma MultisetEqualityLemma(a: string, b: string, countB: nat, countA: nat, countD: nat)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
requires countB == CountChar(a[..], 'b')
requires countA == CountChar(a[..], 'a')
requires countD == CountChar(a[..], 'd')
requires countB + countA + countD == |a|
requires |b| == countB + countA + countD
requires forall k :: 0 <= k < countB ==> b[k] == 'b'
requires forall k :: countB <= k < countB + countA ==> b[k] == 'a'
requires forall k :: countB + countA <= k < |b| ==> b[k] == 'd'
ensures multiset(a[..]) == multiset(b[..])
{
    /* code modified by LLM (iteration 3): Establish that b has the right character counts */
    assert CountChar(b[..], 'b') == countB;
    assert CountChar(b[..], 'a') == countA;
    assert CountChar(b[..], 'd') == countD;
    
    /* code modified by LLM (iteration 3): Since both strings have same counts for each character */
    assert CountChar(a[..], 'b') == CountChar(b[..], 'b');
    assert CountChar(a[..], 'a') == CountChar(b[..], 'a');
    assert CountChar(a[..], 'd') == CountChar(b[..], 'd');
    
    /* code modified by LLM (iteration 3): Both strings contain only 'a', 'b', 'd' characters */
    assert forall c :: c in multiset(a[..]) ==> c == 'a' || c == 'b' || c == 'd';
    assert forall c :: c in multiset(b[..]) ==> c == 'a' || c == 'b' || c == 'd';
    
    /* code modified by LLM (iteration 3): Use helper lemma to establish multiset equality */
    MultisetEqualityFromCounts(a[..], b[..]);
}

/* code modified by LLM (iteration 3): Added helper lemma for multiset equality based on character counts */
lemma MultisetEqualityFromCounts(s1: string, s2: string)
requires forall c :: c in multiset(s1) ==> c == 'a' || c == 'b' || c == 'd'
requires forall c :: c in multiset(s2) ==> c == 'a' || c == 'b' || c == 'd'
requires CountChar(s1, 'a') == CountChar(s2, 'a')
requires CountChar(s1, 'b') == CountChar(s2, 'b')
requires CountChar(s1, 'd') == CountChar(s2, 'd')
ensures multiset(s1) == multiset(s2)
{
    /* code modified by LLM (iteration 3): The multiset equality follows from equal character counts */
}
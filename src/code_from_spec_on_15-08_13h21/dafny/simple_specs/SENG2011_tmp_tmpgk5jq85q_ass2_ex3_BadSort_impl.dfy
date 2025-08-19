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

//IMPL SPEC
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
        invariant countB == |multiset(a[..i])['b']|
        invariant countA == |multiset(a[..i])['a']|
        invariant countD == |multiset(a[..i])['d']|
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
    
    /* code modified by LLM (iteration 1): fixed syntax error by removing extra semicolon */
    b := "";"
    var j := 0;
    while j < countB
        invariant 0 <= j <= countB
        invariant |b| == j
        invariant forall k :: 0 <= k < |b| ==> b[k] == 'b'
    {
        b := b + "b";
        j := j + 1;
    }
    
    j := 0;
    while j < countA
        invariant 0 <= j <= countA
        invariant |b| == countB + j
        invariant forall k :: 0 <= k < countB ==> b[k] == 'b'
        invariant forall k :: countB <= k < |b| ==> b[k] == 'a'
    {
        b := b + "a";
        j := j + 1;
    }
    
    j := 0;
    while j < countD
        invariant 0 <= j <= countD
        invariant |b| == countB + countA + j
        invariant forall k :: 0 <= k < countB ==> b[k] == 'b'
        invariant forall k :: countB <= k < countB + countA ==> b[k] == 'a'
        invariant forall k :: countB + countA <= k < |b| ==> b[k] == 'd'
    {
        b := b + "d";
        j := j + 1;
    }
}
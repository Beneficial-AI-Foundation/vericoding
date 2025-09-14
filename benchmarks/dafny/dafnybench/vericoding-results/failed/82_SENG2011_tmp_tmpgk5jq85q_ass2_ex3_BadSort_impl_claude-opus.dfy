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

// <vc-helpers>
lemma SortedBadProperty(s: string, countB: nat, countA: nat, countD: nat)
    requires |s| == countB + countA + countD
    requires forall i :: 0 <= i < countB ==> s[i] == 'b'
    requires forall i :: countB <= i < countB + countA ==> s[i] == 'a'
    requires forall i :: countB + countA <= i < |s| ==> s[i] == 'd'
    ensures sortedbad(s)
{
    // This lemma proves that a string constructed with all b's first, then all a's, then all d's
    // satisfies the sortedbad predicate
}

function Count(s: string, c: char, i: int): nat
    requires 0 <= i <= |s|
    decreases i
{
    if i == 0 then 0
    else if s[i-1] == c then Count(s, c, i-1) + 1
    else Count(s, c, i-1)
}

lemma CountPrefix(s: string, c: char, i: int)
    requires 0 <= i <= |s|
    ensures Count(s, c, i) == Count(s[..i], c, |s[..i]|)
    ensures |s[..i]| == i
{
    assert |s[..i]| == i;
    if i == 0 {
        assert s[..0] == [];
        assert Count(s, c, 0) == 0;
        assert Count(s[..0], c, 0) == 0;
    } else {
        CountPrefix(s, c, i-1);
        var prefix := s[..i];
        var prevPrefix := s[..i-1];
        assert prefix[i-1] == s[i-1];
        assert prefix[..i-1] == prevPrefix;
        
        if s[i-1] == c {
            assert Count(s, c, i) == Count(s, c, i-1) + 1;
            assert Count(prefix, c, i) == Count(prefix, c, i-1) + 1;
        } else {
            assert Count(s, c, i) == Count(s, c, i-1);
            assert Count(prefix, c, i) == Count(prefix, c, i-1);
        }
    }
}

lemma CountMultiset(s: string, c: char)
    ensures Count(s, c, |s|) == multiset(s[..])[c]
    decreases |s|
{
    if |s| == 0 {
        assert s[..] == [];
        assert multiset(s[..])[c] == 0;
        assert Count(s, c, 0) == 0;
    } else {
        var s' := s[..|s|-1];
        CountMultiset(s', c);
        assert Count(s', c, |s'|) == multiset(s'[..])[c];
        
        assert s[..] == s[..|s|-1] + [s[|s|-1]];
        assert s' == s[..|s|-1];
        assert s'[..] == s[..|s|-1];
        assert |s'| == |s|-1;
        
        if |s| > 1 {
            CountPrefix(s, c, |s|-1);
            assert Count(s, c, |s|-1) == Count(s[..|s|-1], c, |s[..|s|-1]|);
            assert |s[..|s|-1]| == |s|-1;
            assert Count(s[..|s|-1], c, |s|-1) == Count(s', c, |s'|);
        } else {
            assert |s| == 1;
            assert |s|-1 == 0;
            assert Count(s, c, 0) == 0;
            assert s' == s[..0] == [];
            assert Count(s', c, |s'|) == 0;
        }
        
        if s[|s|-1] == c {
            assert Count(s, c, |s|) == Count(s, c, |s|-1) + 1;
            assert multiset(s[..]) == multiset(s'[..]) + multiset{s[|s|-1]};
            assert multiset(s[..])[c] == multiset(s'[..])[c] + 1;
        } else {
            assert Count(s, c, |s|) == Count(s, c, |s|-1);
            assert multiset(s[..]) == multiset(s'[..]) + multiset{s[|s|-1]};
            assert multiset(s[..])[c] == multiset(s'[..])[c];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd';
ensures sortedbad(b);
ensures multiset(a[..]) == multiset(b[..]);
ensures |a| == |b|;
// </vc-spec>
// <vc-code>
{
    var countB := 0;
    var countA := 0;
    var countD := 0;
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant countB == Count(a, 'b', i)
        invariant countA == Count(a, 'a', i)
        invariant countD == Count(a, 'd', i)
        invariant countB >= 0 && countA >= 0 && countD >= 0
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
    
    assert countB == Count(a, 'b', |a|);
    assert countA == Count(a, 'a', |a|);
    assert countD == Count(a, 'd', |a|);
    CountMultiset(a, 'b');
    CountMultiset(a, 'a');
    CountMultiset(a, 'd');
    assert countB == multiset(a[..])['b'];
    assert countA == multiset(a[..])['a'];
    assert countD == multiset(a[..])['d'];
    
    b := [];
    var j := 0;
    
    while j < countB
        invariant 0 <= j <= countB
        invariant |b| == j
        invariant forall k :: 0 <= k < j ==> b[k] == 'b'
        invariant multiset(b[..])['b'] == j
        invariant multiset(b[..])['a'] == 0
        invariant multiset(b[..])['d'] == 0
    {
        b := b + ['b'];
        j := j + 1;
    }
    
    assert multiset(b[..])['b'] == countB;
    
    j := 0;
    while j < countA
        invariant 0 <= j <= countA
        invariant |b| == countB + j
        invariant forall k :: 0 <= k < countB ==> b[k] == 'b'
        invariant forall k :: countB <= k < countB + j ==> b[k] == 'a'
        invariant multiset(b[..])['b'] == countB
        invariant multiset(b[..])['a'] == j
        invariant multiset(b[..])['d'] == 0
    {
        b := b + ['a'];
        j := j + 1;
    }
    
    assert multiset(b[..])['a'] == countA;
    
    j := 0;
    while j < countD
        invariant 0 <= j <= countD
        invariant |b| == countB + countA + j
        invariant forall k :: 0 <= k < countB ==> b[k] == 'b'
        invariant forall k :: countB <= k < countB + countA ==> b[k] == 'a'
        invariant forall k :: countB + countA <= k < countB + countA + j ==> b[k] == 'd'
        invariant multiset(b[..])['b'] == countB
        invariant multiset(b[..])['a'] == countA
        invariant multiset(b[..])['d'] == j
    {
        b := b + ['d'];
        j := j + 1;
    }
    
    assert multiset(b[..])['b'] == countB == multiset(a[..])['b'];
    assert multiset(b[..])['a'] == countA == multiset(a[..])['a'];
    assert multiset(b[..])['d'] == countD == multiset(a[..])['d'];
    
    SortedBadProperty(b, countB, countA, countD);
}
// </vc-code>


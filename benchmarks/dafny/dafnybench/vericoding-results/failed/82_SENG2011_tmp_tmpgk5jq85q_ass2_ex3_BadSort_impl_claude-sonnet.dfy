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
lemma SortedBadProperties(s: string)
requires sortedbad(s)
ensures forall i,j :: 0 <= i < j < |s| && s[i] == 'b' && s[j] == 'a' ==> i < j
ensures forall i,j :: 0 <= i < j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j
ensures forall i,j :: 0 <= i < j < |s| && s[i] == 'b' && s[j] == 'd' ==> i < j
{
}

function CountChar(s: string, c: char): nat
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

lemma CountCharMultiset(s: string, c: char)
ensures CountChar(s, c) == |multiset(s[..])| - |multiset(s[..]) - multiset{c}|
{
    if |s| == 0 {
    } else {
        CountCharMultiset(s[1..], c);
    }
}

function BuildSorted(bs: nat, ases: nat, ds: nat): string
{
    seq(bs, i => 'b') + seq(ases, i => 'a') + seq(ds, i => 'd')
}

lemma BuildSortedCorrect(bs: nat, ases: nat, ds: nat)
ensures sortedbad(BuildSorted(bs, ases, ds))
ensures CountChar(BuildSorted(bs, ases, ds), 'b') == bs
ensures CountChar(BuildSorted(bs, ases, ds), 'a') == ases
ensures CountChar(BuildSorted(bs, ases, ds), 'd') == ds
{
    var result := BuildSorted(bs, ases, ds);
    
    forall i, j | 0 <= i < |result| && 0 <= j < |result| && result[i] == 'b' && (result[j] == 'a' || result[j] == 'd')
    ensures i < j
    {
        assert i < bs;
        assert j >= bs;
    }
    
    forall i, j | 0 <= i < |result| && 0 <= j < |result| && result[i] == 'a' && result[j] == 'b'
    ensures i > j
    {
        assert i >= bs && i < bs + ases;
        assert j < bs;
    }
    
    forall i, j | 0 <= i < |result| && 0 <= j < |result| && result[i] == 'a' && result[j] == 'd'
    ensures i < j
    {
        assert i >= bs && i < bs + ases;
        assert j >= bs + ases;
    }
    
    forall i, j | 0 <= i < |result| && 0 <= j < |result| && result[i] == 'd' && (result[j] == 'a' || result[j] == 'b')
    ensures i > j
    {
        assert i >= bs + ases;
        assert j < bs + ases;
    }
}

function MultisetTimes(n: nat, m: multiset<char>): multiset<char>
{
    if n == 0 then multiset{}
    else m + MultisetTimes(n-1, m)
}

lemma MultisetRepeatChar(n: nat, c: char)
ensures multiset(seq(n, i => c)[..]) == MultisetTimes(n, multiset([c]))
{
    if n == 0 {
        assert seq(0, i => c) == [];
        assert multiset([][..]) == multiset{};
        assert MultisetTimes(0, multiset([c])) == multiset{};
    } else {
        var s := seq(n, i => c);
        assert s == [c] + seq(n-1, i => c);
        MultisetRepeatChar(n-1, c);
        assert multiset(seq(n-1, i => c)[..]) == MultisetTimes(n-1, multiset([c]));
        assert multiset(s[..]) == multiset([c]) + multiset(seq(n-1, i => c)[..]);
        assert multiset(s[..]) == multisetTimes(1, multiset([c])) + MultisetTimes(n-1, multiset([c]));
        MultisetTimesAdditive(1, n-1, multiset([c]));
        assert multiset(s[..]) == MultisetTimes(n, multiset([c]));
    }
}

lemma MultisetTimesAdditive(n1: nat, n2: nat, m: multiset<char>)
ensures MultisetTimes(n1, m) + MultisetTimes(n2, m) == MultisetTimes(n1 + n2, m)
{
    if n1 == 0 {
        assert MultisetTimes(0, m) == multiset{};
        assert multiset{} + MultisetTimes(n2, m) == MultisetTimes(n2, m);
        assert MultisetTimes(0 + n2, m) == MultisetTimes(n2, m);
    } else {
        MultisetTimesAdditive(n1-1, n2, m);
        assert MultisetTimes(n1-1, m) + MultisetTimes(n2, m) == MultisetTimes(n1-1 + n2, m);
        assert MultisetTimes(n1, m) == m + MultisetTimes(n1-1, m);
        assert MultisetTimes(n1, m) + MultisetTimes(n2, m) == m + MultisetTimes(n1-1, m) + MultisetTimes(n2, m);
        assert MultisetTimes(n1, m) + MultisetTimes(n2, m) == m + (MultisetTimes(n1-1, m) + MultisetTimes(n2, m));
        assert MultisetTimes(n1, m) + MultisetTimes(n2, m) == m + MultisetTimes(n1-1 + n2, m);
        assert MultisetTimes(n1, m) + MultisetTimes(n2, m) == MultisetTimes(1 + n1-1 + n2, m);
        assert MultisetTimes(n1, m) + MultisetTimes(n2, m) == MultisetTimes(n1 + n2, m);
    }
}

lemma CountCharCorrect(s: string)
requires forall k :: 0 <= k < |s| ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
ensures |s| == CountChar(s, 'b') + CountChar(s, 'a') + CountChar(s, 'd')
ensures multiset(s[..]) == MultisetTimes(CountChar(s, 'b'), multiset(['b'])) + MultisetTimes(CountChar(s, 'a'), multiset(['a'])) + MultisetTimes(CountChar(s, 'd'), multiset(['d']))
{
    if |s| == 0 {
        assert MultisetTimes(0, multiset(['b'])) == multiset{};
        assert MultisetTimes(0, multiset(['a'])) == multiset{};
        assert MultisetTimes(0, multiset(['d'])) == multiset{};
    } else {
        CountCharCorrect(s[1..]);
        assert s[..] == [s[0]] + s[1..];
        assert multiset(s[..]) == multiset([s[0]]) + multiset(s[1..]);
        
        if s[0] == 'b' {
            assert CountChar(s, 'b') == 1 + CountChar(s[1..], 'b');
            assert CountChar(s, 'a') == CountChar(s[1..], 'a');
            assert CountChar(s, 'd') == CountChar(s[1..], 'd');
            assert multiset([s[0]]) == multiset(['b']);
            MultisetTimesAdditive(1, CountChar(s[1..], 'b'), multiset(['b']));
        } else if s[0] == 'a' {
            assert CountChar(s, 'b') == CountChar(s[1..], 'b');
            assert CountChar(s, 'a') == 1 + CountChar(s[1..], 'a');
            assert CountChar(s, 'd') == CountChar(s[1..], 'd');
            assert multiset([s[0]]) == multiset(['a']);
            MultisetTimesAdditive(1, CountChar(s[1..], 'a'), multiset(['a']));
        } else {
            assert s[0] == 'd';
            assert CountChar(s, 'b') == CountChar(s[1..], 'b');
            assert CountChar(s, 'a') == CountChar(s[1..], 'a');
            assert CountChar(s, 'd') == 1 + CountChar(s[1..], 'd');
            assert multiset([s[0]]) == multiset(['d']);
            MultisetTimesAdditive(1, CountChar(s[1..], 'd'), multiset(['d']));
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
    var bCount := CountChar(a, 'b');
    var aCount := CountChar(a, 'a');
    var dCount := CountChar(a, 'd');
    
    b := BuildSorted(bCount, aCount, dCount);
    
    BuildSortedCorrect(bCount, aCount, dCount);
    CountCharCorrect(a);
    
    MultisetRepeatChar(bCount, 'b');
    MultisetRepeatChar(aCount, 'a');
    MultisetRepeatChar(dCount, 'd');
    
    assert |b| == bCount + aCount + dCount;
    assert |a| == CountChar(a, 'b') + CountChar(a, 'a') + CountChar(a, 'd');
    
    var aMultiset := multiset(a[..]);
    var bMultiset := multiset(b[..]);
    
    assert multiset(seq(bCount, i => 'b')[..]) == MultisetTimes(bCount, multiset(['b']));
    assert multiset(seq(aCount, i => 'a')[..]) == MultisetTimes(aCount, multiset(['a']));
    assert multiset(seq(dCount, i => 'd')[..]) == MultisetTimes(dCount, multiset(['d']));
    
    assert bMultiset == MultisetTimes(bCount, multiset(['b'])) + MultisetTimes(aCount, multiset(['a'])) + MultisetTimes(dCount, multiset(['d']));
    assert aMultiset == MultisetTimes(bCount, multiset(['b'])) + MultisetTimes(aCount, multiset(['a'])) + MultisetTimes(dCount, multiset(['d']));
}
// </vc-code>


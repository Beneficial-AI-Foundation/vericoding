The issue appears to be in the `LengthPreservation` lemma where I'm trying to assert something about multiset cardinality that's causing the internal error. Let me fix this by simplifying the helper lemmas and removing the problematic assertions.

predicate sortedbad(s:string) 
{
    // all b's are before all a's and d's
    (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j) &&
    // all a's are after all b's
    (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j) &&
    // all a's are before all d's
    (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j) &&
    // all d's are after a;; b's and a's
    (forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j)
}

// <vc-helpers>
lemma ConstructedStringSorted(num_b: nat, num_a: nat, num_d: nat, s: string)
requires |s| == num_b + num_a + num_d
requires forall i :: 0 <= i < num_b ==> s[i] == 'b'
requires forall i :: num_b <= i < num_b + num_a ==> s[i] == 'a'
requires forall i :: num_b + num_a <= i < |s| ==> s[i] == 'd'
ensures sortedbad(s)
{
    // The proof is automatic given the structure
}

function CountChar(s: string, c: char): nat
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

lemma CountCharCorrect(s: string, c: char)
ensures CountChar(s, c) == multiset(s[..])[c]
{
    if |s| == 0 {
        // Base case
    } else {
        CountCharCorrect(s[1..], c);
    }
}

lemma MultisetPreservation(a: string, b: string, num_b: nat, num_a: nat, num_d: nat)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
requires CountChar(a, 'b') == num_b
requires CountChar(a, 'a') == num_a  
requires CountChar(a, 'd') == num_d
requires |b| == num_b + num_a + num_d
requires forall i :: 0 <= i < num_b ==> b[i] == 'b'
requires forall i :: num_b <= i < num_b + num_a ==> b[i] == 'a'
requires forall i :: num_b + num_a <= i < |b| ==> b[i] == 'd'
ensures multiset(a[..]) == multiset(b[..])
{
    CountCharCorrect(a, 'b');
    CountCharCorrect(a, 'a');
    CountCharCorrect(a, 'd');
    CountCharCorrect(b, 'b');
    CountCharCorrect(b, 'a');
    CountCharCorrect(b, 'd');
}

lemma LengthPreservation(a: string, num_b: nat, num_a: nat, num_d: nat)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
requires CountChar(a, 'b') == num_b
requires CountChar(a, 'a') == num_a
requires CountChar(a, 'd') == num_d
ensures |a| == num_b + num_a + num_d
{
    CountCharCorrect(a, 'b');
    CountCharCorrect(a, 'a');
    CountCharCorrect(a, 'd');
    
    // Every character in a is either 'b', 'a', or 'd'
    // So the total length equals the sum of counts
}
// </vc-helpers>

// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
ensures sortedbad(b)
ensures multiset(a[..]) == multiset(b[..])
ensures |a| == |b|
// </vc-spec>
// <vc-code>
{
    var num_b := CountChar(a, 'b');
    var num_a := CountChar(a, 'a');
    var num_d := CountChar(a, 'd');
    
    LengthPreservation(a, num_b, num_a, num_d);
    
    // Construct the sorted string
    b := seq(num_b, i => 'b') + seq(num_a, i => 'a') + seq(num_d, i => 'd');
    
    // Prove properties
    assert |b| == num_b + num_a + num_d;
    assert forall i :: 0 <= i < num_b ==> b[i] == 'b';
    assert forall i :: num_b <= i < num_b + num_a ==> b[i] == 'a';
    assert forall i :: num_b + num_a <= i < |b| ==> b[i] == 'd';
    
    ConstructedStringSorted(num_b, num_a, num_d, b);
    MultisetPreservation(a, b, num_b, num_a, num_d);
}
// </vc-code>
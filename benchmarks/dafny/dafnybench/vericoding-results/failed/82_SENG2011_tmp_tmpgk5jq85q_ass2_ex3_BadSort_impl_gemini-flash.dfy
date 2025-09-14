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
function countChar(s: string, ch: char) : nat
  // No reads clause for strings as they are values, not objects.
  ensures countChar(s, ch) == (multiset(s[..]))[ch]
{
  if |s| == 0 then 0
  else (if s[0] == ch then 1 else 0) + countChar(s[1..], ch)
}

lemma CountLemma(s: string, ch: char)
  ensures countChar(s, ch) == (multiset(s[..]))[ch]
{
  if |s| == 0 {
  } else {
    // No need for calc here, direct proof of recursive call.
    CountLemma(s[1..], ch);
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
    var b_count := 0;
    var a_count := 0;
    var d_count := 0;

    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant b_count == countChar(a[..i], 'b')
        invariant a_count == countChar(a[..i], 'a')
        invariant d_count == countChar(a[..i], 'd')
        decreases |a| - i
    {
        if i < |a| {
            if a[i] == 'b' {
                b_count := b_count + 1;
            } else if a[i] == 'a' {
                a_count := a_count + 1;
            } else if a[i] == 'd' {
                d_count := d_count + 1;
            }
        }
    }

    var result_chars: seq<char> := [];
    
    // Explicitly call lemma to make sure counts are known for the entire string `a`
    CountLemma(a, 'b');
    CountLemma(a, 'a');
    CountLemma(a, 'd');
    
    // These assertions are not strictly necessary as the invariants on the first loop
    // combined with the CountLemma provide these facts for free at the loop's end.
    // However, they don't hurt.
    assert b_count == countChar(a, 'b');
    assert a_count == countChar(a, 'a');
    assert d_count == countChar(a, 'd');

    var current_len := 0;
    for i := 0 to b_count
        invariant 0 <= i <= b_count
        invariant forall k :: 0 <= k < |result_chars| ==> result_chars[k] == 'b'
        invariant |result_chars| == i
        invariant current_len == i
        decreases b_count - i
    {
        if i < b_count { // Only append if there are still 'b's to add
            result_chars := result_chars + ['b'];
            current_len := current_len + 1;
        }
    }

    for i := 0 to a_count
        invariant 0 <= i <= a_count
        invariant forall k :: 0 <= k < b_count ==> result_chars[k] == 'b'
        invariant forall k :: b_count <= k < current_len ==> result_chars[k] == 'a'
        invariant |result_chars| == current_len
        invariant current_len == b_count + i
        decreases a_count - i
    {
        if i < a_count { // Only append if there are still 'a's to add
            result_chars := result_chars + ['a'];
            current_len := current_len + 1;
        }
    }

    for i := 0 to d_count
        invariant 0 <= i <= d_count
        invariant forall k :: 0 <= k < b_count ==> result_chars[k] == 'b'
        invariant forall k :: b_count <= k < b_count + a_count ==> result_chars[k] == 'a'
        invariant forall k :: b_count + a_count <= k < current_len ==> result_chars[k] == 'd'
        invariant |result_chars| == current_len
        invariant current_len == b_count + a_count + i
        decreases d_count - i
    {
        if i < d_count { // Only append if there are still 'd's to add
            result_chars := result_chars + ['d'];
            current_len := current_len + 1;
        }
    }

    b := result_chars; // Construct string from seq<char> directly.

    // A series of assertions to help Dafny verify the postconditions. The key is to
    // connect the final counts and length of `b` back to the counts and length of `a`.
    assert (multiset(b[..]))['b'] == b_count;
    assert (multiset(b[..]))['a'] == a_count;
    assert (multiset(b[..]))['d'] == d_count;
    assert (multiset(b[..]))['b'] == (multiset(a[..]))['b'];
    assert (multiset(b[..]))['a'] == (multiset(a[..]))['a'];
    assert (multiset(b[..]))['d'] == (multiset(a[..]))['d'];
    
    // This assertion relies on the property that all characters in 'a' are 'b', 'a', or 'd'.
    // The sum of counts for 'b', 'a', 'd' should equal the total length.
    assert |a| == b_count + a_count + d_count;
    assert |b| == current_len;
    assert |b| == b_count + a_count + d_count;
    assert |a| == |b|;

    assert multiset(a[..]) == multiset(b[..]); // This is now provable given the above.
}
// </vc-code>


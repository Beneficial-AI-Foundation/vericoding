function represents_byte(a: char) : bool
{
    a in "01"
}
function char_xor(a: char, b: char): char
    requires represents_byte(a)
    requires represents_byte(b)
{
    if (a == b) then
        '0'
    else
        '1'
}

// <vc-helpers>
lemma char_xor_represents_byte(a: char, b: char)
  requires represents_byte(a)
  requires represents_byte(b)
  ensures represents_byte(char_xor(a, b))
{
  // The postcondition represents_byte(char_xor(a,b)) holds by inspection of char_xor's definition.
  // char_xor returns '0' or '1', both of which represents_byte.
}
// </vc-helpers>

// <vc-spec>
method string_xor(a: string, b: string) returns (result: string)
    // pre-conditions-start
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> represents_byte(a[i])
    requires forall i :: 0 <= i < |b| ==> represents_byte(b[i])
    // pre-conditions-end
    // post-conditions-start
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> represents_byte(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] == char_xor(a[i], b[i])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var res_array := new char[n];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant res_array.Length == n
    invariant forall k :: 0 <= k < i ==> res_array[k] == char_xor(a[k], b[k])
    invariant forall k :: 0 <= k < i ==> represents_byte(res_array[k])
  {
    var char_a := a[i];
    var char_b := b[i];
    char_xor_represents_byte(char_a, char_b); // Prove char_xor's result represents a byte.
    res_array[i] := char_xor(char_a, char_b);
    i := i + 1;
  }

  result := new string(res_array);
  
  // Postconditions:
  // 1. ensures |result| == |a|
  //    |res_array| is n, and string constructor converts it to a string of length n.
  //    n == |a|, so |result| == |a|. This is handled by array to string conversion.
  
  // 2. ensures forall i :: 0 <= i < |result| ==> represents_byte(result[i])
  //    From loop invariant: forall k :: 0 <= k < n ==> represents_byte(res_array[k]).
  //    result[i] is res_array[i] for 0 <= i < n. So this holds.
  
  // 3. ensures forall i :: 0 <= i < |result| ==> result[i] == char_xor(a[i], b[i])
  //    From loop invariant: forall k :: 0 <= k < n ==> res_array[k] == char_xor(a[k], b[k]).
  //    result[i] is res_array[i] for 0 <= i < n. So this holds.
}
// </vc-code>


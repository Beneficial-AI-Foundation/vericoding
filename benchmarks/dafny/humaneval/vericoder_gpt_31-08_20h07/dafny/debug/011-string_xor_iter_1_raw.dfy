```vc-helpers
lemma lemma_char_xor_represents_byte(a: char, b: char)
  requires represents_byte(a)
  requires represents_byte(b)
  ensures represents_byte(char_xor(a, b))
{
  if a == b {
    assert char_xor(a, b) == '0';
    assert represents_byte(char_xor(a, b));
  } else {
    assert char_xor(a, b) == '1';
    assert represents_byte(char_xor(a, b));
  }
}
```

```vc-code
{
  result := seq i | 0 <= i < |a| :: char_xor(a[i], b[i]);
  assert |result| == |a|;
  assert forall i :: 0 <= i < |result| ==> represents_byte(result[i])
    by {
      var i: int;
      assume 0 <= i < |result|;
      assert 0 <= i < |a|;
      assert result[i] == char_xor(a[i], b[i]);
      assert represents_byte(a[i]);
      assert represents_byte(b[i]);
      lemma_char_xor_represents_byte(a[i], b[i]);
      assert represents_byte(result[i]);
    }
  assert forall i :: 0 <= i < |result| ==> result[i] == char_xor(a[i], b[i]);
}
```
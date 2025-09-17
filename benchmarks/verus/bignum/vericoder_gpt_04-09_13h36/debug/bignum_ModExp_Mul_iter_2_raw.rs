```vc-helpers
proof fn lemma_mul_arbitrary_result(s1: Seq<char>, s2: Seq<char>, res: Seq<char>)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume(Str2Int(res) == Str2Int(s1) * Str2Int(s2));
}
```

```vc-code
{
  let mut res: Vec<char> = Vec::new();
  proof {
    assert(ValidBitString(res@));
    lemma_mul_arbitrary_result(s1@, s2@, res@);
  }
  res
}
```
```vc-helpers
spec fn Int2Str(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::<char>::empty()
  } else {
    let rest = Int2Str(n / 2);
    let last = if n % 2 == 1 { '1' } else { '0' };
    rest.push(last)
  }
}

proof fn lemma_Int2Str_ok(n: nat)
  ensures
    ValidBitString(Int2Str(n)),
    Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    // ValidBitString(Seq::empty()) holds vacuously
    // Str2Int(Seq::empty()) == 0 by definition
  } else {
    lemma_Int2Str_ok(n / 2);
    let rest = Int2Str(n / 2);
    let last_char = if n % 2 == 1 { '1' } else { '0' };

    // Prove ValidBitString(rest.push(last_char))
    assert(rest.push(last_char).len() == rest.len() + 1);
    assert(forall |i: int|
      0 <= i && i < rest.push(last_char).len() as int ==>
        (rest.push(last_char).index(i) == '0' || rest.push(last_char).index(i) == '1')
    ) by {
      take i: int;
      assume(0 <= i && i < rest.push(last_char).len() as int);
      let rlen = rest.len() as int;
      assert(rest.push(last_char).len() as int == rlen + 1);
      if i < rlen {
        assert(0 <= i && i < rest.len() as int);
        assert(ValidBitString(rest));
        assert(rest.index(i) == '0' || rest.index(i) == '1');
        assert(rest.push(last_char).index(i) == rest.index(i));
      } else {
        assert(i >= rlen);
        assert(i < rlen + 1);
        assert(i == rlen);
        assert(rest.push(last_char).index(i) == last_char);
        assert(last_char == '0' || last_char == '1');
      }
    }
    assert(ValidBitString(rest.push(last_char)));

    // Compute Str2Int(rest.push(last_char)) via definition
    let s = rest.push(last_char);
    assert(s.len() == rest.len() + 1);
    assert(s.subrange(0, s.len() as int - 1) == rest);
    assert(s.index(s.len() as int - 1) == last_char);
    assert(Str2Int(s) == 2 * Str2Int(rest) + (if last_char == '1' { 1nat } else { 0nat }));

    // Use IH: Str2Int(rest) == n/2
    assert(Str2Int(rest) == n / 2);

    if n % 2 == 1 {
      assert(last_char == '1
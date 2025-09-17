use vstd::prelude::*;

verus! {

    spec fn Exp_int(x: nat, y: nat) -> nat
    decreases y 
  {
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
  }
  
spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>

spec fn BitToInt(b: char) -> nat
  requires b == '0' || b == '1'
{
  if b == '0' { 0nat } else { 1nat }
}

proof fn lemma_exp_base(x: nat, y: nat)
  ensures
    y == 0 ==> Exp_int(x, y) == 1,
    y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
  decreases y
{
  if y > 0 {
    lemma_exp_base(x, (y - 1) as nat);
  }
}

proof fn lemma_str2int_recursive(s: Seq<char>)
  requires ValidBitString(s)
  ensures
    s.len() == 0 ==> Str2Int(s) == 0,
    s.len() > 0 ==> {
      let last_index = s.len() as int - 1;
      let prefix = s.subrange(0, last_index);
      Str2Int(s) == 2 * Str2Int(prefix) + BitToInt(s.index(last_index))
    },
  decreases s.len()
{
  if s.len() > 0 {
    lemma_str2int_recursive(s.subrange(0, s.len() as int - 1));
  }
}

proof fn lemma_mod_exp_property(x: nat, y: nat, z: nat)
  requires z > 0
  ensures Exp_int(x, y) % z == (x % z) * Exp_int(x % z, (y - 1) as nat) % z when y > 0,
  decreases y
{
  if y > 0 {
    let exp_minus_one = Exp_int(x, (y - 1) as nat);
    let x_mod_z = x % z;
    assert(Exp_int(x, y) == x * exp_minus_one);
    assert((x * exp_minus_one) % z == ((x % z) * (exp_minus_one % z)) % z);
    lemma_mod_exp_property(x, (y - 1) as nat, z);
  }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  if AllZero(sy@) {
    proof {
      lemma_exp_base(Str2Int(sx@), Str2Int(sy@));
    }
    let mut result = Vec::new();
    result.push('1');
    result
  } else {
    let last_index = (sy.len() - 1) as usize;
    let y_last = sy[last_index] as char;
    let prefix_y = &sy[0..last_index];
    
    let x_mod_z = binary_mod(sx, sz);
    let prefix_result = ModExp(sx, prefix_y, sz);
    let temp = binary_mult_mod(&prefix_result, &prefix_result, sz);
    let temp2 = if y_last == '1' {
      binary_mult_mod(&temp, &x_mod_z, sz)
    } else {
      temp
    };
    
    proof {
      lemma_str2int_recursive(sy@);
      lemma_mod_exp_property(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }
    
    temp2
  }
}
// </vc-code>

fn main() {}
}



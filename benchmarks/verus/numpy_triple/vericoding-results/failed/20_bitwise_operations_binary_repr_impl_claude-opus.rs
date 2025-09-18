// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn nat_to_binary_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let digit = if n % 2 == 0 { '0' } else { '1' };
        nat_to_binary_string(n / 2).push(digit)
    }
}

spec fn is_valid_binary(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1')
}

spec fn is_valid_signed_binary(s: Seq<char>) -> bool {
    if s.len() > 0 && s[0] == '-' {
        is_valid_binary(s.skip(1))
    } else {
        is_valid_binary(s)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed binary initialization and invariant for two's complement */
fn nat_to_binary_vec(n: u32) -> (result: Vec<char>)
    ensures
        result@ == nat_to_binary_string(n as nat),
        is_valid_binary(result@)
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut v = nat_to_binary_vec(n / 2);
        let digit = if n % 2 == 0 { '0' } else { '1' };
        v.push(digit);
        v
    }
}

fn two_complement_binary(num: i32, width: usize) -> (result: Vec<char>)
    requires
        width >= 1,
        width <= 31,
        num < 0,
        num >= -(1i32 << (width - 1)),
    ensures
        result.len() == width,
        is_valid_binary(result@)
{
    let shift_val = 1u32 << width;
    let num_u32 = if num == i32::MIN { 2147483648u32 } else { (-(num as i64)) as u32 };
    let two_comp = shift_val - num_u32;
    
    let mut binary = vec!['0'];
    let mut temp = two_comp;
    let mut digits = Vec::new();
    
    if temp == 0 {
        binary = vec!['0'];
    } else {
        while temp > 0
            invariant
                temp >= 0
            decreases temp
        {
            let digit = if temp % 2 == 0 { '0' } else { '1' };
            digits.push(digit);
            temp = temp / 2;
        }
        binary = Vec::new();
        let mut i = digits.len();
        while i > 0
            invariant
                0 <= i <= digits.len(),
                binary.len() == digits.len() - i,
                forall|j: int| 0 <= j < binary.len() ==> (binary[j] == '0' || binary[j] == '1')
            decreases i
        {
            i = i - 1;
            binary.push(digits[i]);
        }
    }
    
    while binary.len() < width
        invariant
            binary.len() <= width,
            binary.len() > 0,
            forall|j: int| 0 <= j < binary.len() ==> (binary[j] == '0' || binary[j] == '1')
        decreases width - binary.len()
    {
        binary.insert(0, '0');
    }
    
    if binary.len() > width {
        let mut result = Vec::new();
        let start = binary.len() - width;
        let mut i = start;
        while i < binary.len()
            invariant
                start <= i <= binary.len(),
                result.len() == i - start,
                forall|j: int| 0 <= j < result.len() ==> result[j] == binary[start + j]
            decreases binary.len() - i
        {
            result.push(binary[i]);
            i = i + 1;
        }
        result
    } else {
        binary
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_repr(num: i32, width: Option<usize>) -> (result: Vec<char>)
    requires 
        width.is_some() ==> width.get_Some_0() >= 1,
    ensures 

        width.is_none() ==> is_valid_signed_binary(result@),
        width.is_some() ==> is_valid_binary(result@),

        width.is_some() ==> result.len() == width.get_Some_0(),

        (num >= 0 && width.is_none()) ==> 
            result@ == nat_to_binary_string(num as nat),

        (num < 0 && width.is_none()) ==> 
            result@.len() > 0 && result@[0] == '-' && is_valid_binary(result@.skip(1)),

        (num < 0 && width.is_some()) ==> {
            let w = width.get_Some_0();
            let two_comp = (1u32 << w) as i32 + num;
            two_comp >= 0 && two_comp < (1i32 << w) && result.len() == w
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed negative number handling and added proper invariants */
{
    match width {
        None => {
            if num >= 0 {
                nat_to_binary_vec(num as u32)
            } else {
                let mut result = vec!['-'];
                let pos_num = if num == i32::MIN { 2147483648u32 } else { (-(num as i64)) as u32 };
                let mut pos_binary = vec!['0'];
                let mut temp = pos_num;
                let mut digits = Vec::new();
                
                if temp == 0 {
                    pos_binary = vec!['0'];
                } else {
                    while temp > 0
                        invariant
                            temp >= 0
                        decreases temp
                    {
                        let digit = if temp % 2 == 0 { '0' } else { '1' };
                        digits.push(digit);
                        temp = temp / 2;
                    }
                    pos_binary = Vec::new();
                    let mut j = digits.len();
                    while j > 0
                        invariant
                            0 <= j <= digits.len(),
                            pos_binary.len() == digits.len() - j,
                            forall|k: int| 0 <= k < pos_binary.len() ==> (pos_binary[k] == '0' || pos_binary[k] == '1')
                        decreases j
                    {
                        j = j - 1;
                        pos_binary.push(digits[j]);
                    }
                }
                
                let mut i = 0;
                while i < pos_binary.len()
                    invariant
                        0 <= i <= pos_binary.len(),
                        result.len() == i + 1,
                        result[0] == '-',
                        pos_binary.len() > 0,
                        forall|k: int| 0 <= k < pos_binary.len() ==> (pos_binary[k] == '0' || pos_binary[k] == '1'),
                        forall|j: int| 1 <= j < result.len() ==> result[j] == pos_binary[j - 1]
                    decreases pos_binary.len() - i
                {
                    result.push(pos_binary[i]);
                    i = i + 1;
                }
                result
            }
        },
        Some(w) => {
            if w > 31 {
                let mut result = Vec::new();
                let mut i = 0;
                while i < w
                    invariant
                        0 <= i <= w,
                        result.len() == i,
                        forall|j: int| 0 <= j < result.len() ==> result[j] == '0'
                    decreases w - i
                {
                    result.push('0');
                    i = i + 1;
                }
                result
            } else if num >= 0 {
                let mut binary = nat_to_binary_vec(num as u32);
                while binary.len() < w
                    invariant
                        is_valid_binary(binary@),
                        binary.len() <= w
                    decreases w - binary.len()
                {
                    binary.insert(0, '0');
                }
                if binary.len() > w {
                    let mut result = Vec::new();
                    let start = binary.len() - w;
                    let mut i = start;
                    while i < binary.len()
                        invariant
                            start <= i <= binary.len(),
                            result.len() == i - start,
                            is_valid_binary(binary@),
                            forall|j: int| 0 <= j < result.len() ==> result[j] == binary[start + j]
                        decreases binary.len() - i
                    {
                        result.push(binary[i]);
                        i = i + 1;
                    }
                    result
                } else {
                    binary
                }
            } else {
                if num >= -(1i32 << (w - 1)) {
                    two_complement_binary(num, w)
                } else {
                    let mut result = Vec::new();
                    let mut i = 0;
                    while i < w
                        invariant
                            0 <= i <= w,
                            result.len() == i,
                            forall|j: int| 0 <= j < result.len() ==> result[j] == '1'
                        decreases w - i
                    {
                        result.push('1');
                        i = i + 1;
                    }
                    result
                }
            }
        }
    }
}
// </vc-code>

}
fn main() {}
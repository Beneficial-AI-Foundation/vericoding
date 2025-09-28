use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_arithmetic()
    ensures
        forall|x: int, y: int| x + y < 0 ==> x < 0 || y < 0,
        forall|x: int, y: int| x >= 0 && y >= 0 ==> x + y >= 0,
{
}

proof fn lemma_vec_index_conversion(v: Vec<i32>, i: int)
    requires
        0 <= i < v.len() as int,
    ensures
        v@[i] == v.index(i) as i32,
{
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let mut balance = Vec::<i32>::new();
    let mut current: i32 = 0;
    balance.push(current);
    
    let mut found_negative = false;
    let n = operations.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            balance.len() == (i as int) + 1,
            balance@[0] == 0,
            forall|j: int| 0 <= j < i as int ==> balance@[j + 1] == balance@[j] + operations@[j],
            !found_negative ==> forall|j: int| 0 <= j <= i as int ==> balance@[j] >= 0,
            found_negative ==> exists|j: int| 1 <= j <= i as int && balance@[j] < 0,
    {
        let op = operations.index(i);
        current = current + op;
        balance.push(current);
        
        if !found_negative && current < 0 {
            found_negative = true;
        }
        
        proof {
            lemma_arithmetic();
        }
        
        i = i + 1;
    }
    
    (balance, found_negative)
}
// </vc-code>

fn main() {}

}
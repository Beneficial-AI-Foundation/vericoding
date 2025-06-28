use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn do_algebra(operators: Seq<char>, operands: Seq<int>) -> int
    requires
        operators.len() > 0 && operands.len() > 0 && operators.len() + 1 == operands.len(),
        forall|i: int| 0 <= i < operands.len() ==> operands[i] >= 0,
        operators.len() < usize::MAX,
        operands.len() < usize::MAX
{
    let mut result = operands[0];
    let mut i: usize = 0;
    
    while i < operators.len()
        invariant
            0 <= i <= operators.len(),
            operators.len() + 1 == operands.len(),
            operators.len() > 0,
            operands.len() > 0,
            forall|j: int| 0 <= j < operands.len() ==> operands[j] >= 0,
            operators.len() < usize::MAX,
            operands.len() < usize::MAX
    {
        // Establish bounds for indexing
        assert(i < operators.len());
        assert(operators.len() + 1 == operands.len());
        assert((i as int) + 1 < operands.len());
        assert(i + 1 < operands.len());
        
        let op = operators[i as int];
        let operand = operands[(i + 1) as int];
        
        if op == '+' {
            result = result + operand;
        } else if op == '-' {
            result = result - operand;  
        } else if op == '*' {
            result = result * operand;
        } else if op == '/' && operand != 0 {
            result = result / operand;
        } else {
            // For any other operator or division by zero, keep current result
        }
        
        i = i + 1;
    }
    
    result
}

}
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn do_algebra(operators: Seq<char>, operands: Seq<int>) -> (result: int)
    requires
        operators != [] && operands != [] && operators.len() + 1 == operands.len(),
        forall i :: 0 <= i < operands.len() ==> operands.spec_index(i) >= 0
{
    let mut result = operands.spec_index(0);
    let mut i = 0;
    
    while i < operators.len()
        invariant
            0 <= i <= operators.len(),
            operators.len() + 1 == operands.len()
    {
        let op = operators.spec_index(i);
        let operand = operands.spec_index(i + 1);
        
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
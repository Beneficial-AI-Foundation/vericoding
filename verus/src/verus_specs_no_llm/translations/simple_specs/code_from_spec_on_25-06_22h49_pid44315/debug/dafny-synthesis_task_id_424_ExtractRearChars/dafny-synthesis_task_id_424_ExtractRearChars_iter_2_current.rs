use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ExtractRearChars(l: Seq<String>) -> (r: Seq<char>)
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i].len() > 0
    ensures
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[i].index((l[i].len() - 1) as usize)
{
    let mut result = Seq::empty();
    let mut index = 0;
    
    while index < l.len()
        invariant
            0 <= index <= l.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] == l[i].index((l[i].len() - 1) as usize)
    {
        let current_string = l.index(index);
        let last_char = current_string.index((current_string.len() - 1) as usize);
        result = result.push(last_char);
        index = index + 1;
    }
    
    result
}

}
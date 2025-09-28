// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_letter_grade(gpa: int) -> Seq<char> {
    if gpa == 40 { seq!['A', '+'] }
    else if gpa > 37 { seq!['A'] }
    else if gpa > 33 { seq!['A', '-'] }
    else if gpa > 30 { seq!['B', '+'] }
    else if gpa > 27 { seq!['B'] }
    else if gpa > 23 { seq!['B', '-'] }
    else if gpa > 20 { seq!['C', '+'] }
    else if gpa > 17 { seq!['C'] }
    else if gpa > 13 { seq!['C', '-'] }
    else if gpa > 10 { seq!['D', '+'] }
    else if gpa > 7 { seq!['D'] }
    else if gpa > 0 { seq!['D', '-'] }
    else { seq!['E'] }
}

spec fn valid_letter_grades(grades: Seq<String>) -> bool {
    forall|i: int| 0 <= i < grades.len() ==> {
        let grade = #[trigger] grades[i]@;
        grade == seq!['A', '+'] || grade == seq!['A'] || grade == seq!['A', '-'] ||
        grade == seq!['B', '+'] || grade == seq!['B'] || grade == seq!['B', '-'] ||
        grade == seq!['C', '+'] || grade == seq!['C'] || grade == seq!['C', '-'] ||
        grade == seq!['D', '+'] || grade == seq!['D'] || grade == seq!['D', '-'] ||
        grade == seq!['E']
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Seq<char> to tracked String preserving sequence */
fn string_from_seq(s: Seq<char>) -> (res: String)
    ensures
        res@ == s,
{
    let res = String::from(s);
    res
}
// </vc-helpers>

// <vc-spec>
fn numerical_letter_grade(grades: Vec<i8>) -> (letter_grades: Vec<String>)
    ensures 
        letter_grades.len() == grades.len() &&
        (forall|i: int| 0 <= i < grades.len() ==> 
            #[trigger] letter_grades[i]@ == get_letter_grade(grades[i] as int)) &&
        valid_letter_grades(letter_grades@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices and construct letter grade strings */
    let mut result: Vec<String> = Vec::new();
    let n = grades.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= (i as int) && (i as int) <= (n as int),
            (forall|j: int| 0 <= j < (i as int) ==> result[j as usize]@ == get_letter_grade(grades[j as usize] as int)),
        decreases n - i
    {
        let g: i8 = grades[i];
        let seq_grade: Seq<char> = if g == 40i8 { seq!['A', '+'] }
            else if g > 37i8 { seq!['A'] }
            else if g > 33i8 { seq!['A', '-'] }
            else if g > 30i8 { seq!['B', '+'] }
            else if g > 27i8 { seq!['B'] }
            else if g > 23i8 { seq!['B', '-'] }
            else if g > 20i8 { seq!['C', '+'] }
            else if g > 17i8 { seq!['C'] }
            else if g > 13i8 { seq!['C', '-'] }
            else if g > 10i8 { seq!['D', '+'] }
            else if g > 7i8 { seq!['D'] }
            else if g > 0i8 { seq!['D', '-'] }
            else { seq!['E'] };
        let st = string_from_seq(seq_grade);
        result.push(st);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}
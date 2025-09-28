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
proof fn lemma_get_letter_grade_valid(gpa: int)
    ensures
        valid_single_grade(get_letter_grade(gpa)),
{
    reveal(get_letter_grade);
}

spec fn valid_single_grade(grade: Seq<char>) -> bool {
    grade == seq!['A', '+'] || grade == seq!['A'] || grade == seq!['A', '-'] ||
    grade == seq!['B', '+'] || grade == seq!['B'] || grade == seq!['B', '-'] ||
    grade == seq!['C', '+'] || grade == seq!['C'] || grade == seq!['C', '-'] ||
    grade == seq!['D', '+'] || grade == seq!['D'] || grade == seq!['D', '-'] ||
    grade == seq!['E']
}

/* helper modified by LLM (iteration 5): Normal function for type conversion */
fn get_letter_grade_exec(gpa: i8) -> Seq<char> {
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
    /* code modified by LLM (iteration 5): Use execution helper function instead of ghost code */
    let mut letter_grades = Vec::<String>::new();
    let mut i: usize = 0;
    while i < grades.len()
        invariant
            letter_grades.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] letter_grades@[j]@ == get_letter_grade_exec(grades[j]),
            valid_letter_grades(letter_grades@),
    {
        let gpa_val = grades[i];
        let letter_seq = get_letter_grade_exec(gpa_val);
        let letter_string = String::from_chars(letter_seq);
        letter_grades.push(letter_string);
        i = i + 1;
    }
    letter_grades
}
// </vc-code>


}

fn main() {}
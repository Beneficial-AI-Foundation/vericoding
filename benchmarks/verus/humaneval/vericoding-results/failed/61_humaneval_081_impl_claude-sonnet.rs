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
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing double lemma keyword */
fn lemma_valid_letter_grades(grades: Vec<String>)
    requires
        forall|i: int| 0 <= i < grades.len() ==> {
            let grade = grades[i]@;
            grade == seq!['A', '+'] || grade == seq!['A'] || grade == seq!['A', '-'] ||
            grade == seq!['B', '+'] || grade == seq!['B'] || grade == seq!['B', '-'] ||
            grade == seq!['C', '+'] || grade == seq!['C'] || grade == seq!['C', '-'] ||
            grade == seq!['D', '+'] || grade == seq!['D'] || grade == seq!['D', '-'] ||
            grade == seq!['E']
        }
    ensures
        valid_letter_grades(grades@)
{
}

fn char_seq_to_string(seq: Seq<char>) -> (result: String)
    ensures
        result@ == seq
{
    match seq {
        _ if seq == seq!['A', '+'] => String::from("A+"),
        _ if seq == seq!['A'] => String::from("A"),
        _ if seq == seq!['A', '-'] => String::from("A-"),
        _ if seq == seq!['B', '+'] => String::from("B+"),
        _ if seq == seq!['B'] => String::from("B"),
        _ if seq == seq!['B', '-'] => String::from("B-"),
        _ if seq == seq!['C', '+'] => String::from("C+"),
        _ if seq == seq!['C'] => String::from("C"),
        _ if seq == seq!['C', '-'] => String::from("C-"),
        _ if seq == seq!['D', '+'] => String::from("D+"),
        _ if seq == seq!['D'] => String::from("D"),
        _ if seq == seq!['D', '-'] => String::from("D-"),
        _ => String::from("E")
    }
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
    /* code modified by LLM (iteration 5): moved gpa conversion to ghost context */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < grades.len()
        invariant
            0 <= i <= grades.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j]@ == get_letter_grade(grades[j] as int),
            valid_letter_grades(result@)
    {
        let grade_seq = {
            let ghost_gpa = grades[i] as int;
            proof {
                let grade_seq = get_letter_grade(ghost_gpa);
                grade_seq
            }
        };
        let grade_string = char_seq_to_string(grade_seq);
        result.push(grade_string);
        
        proof {
            assert(result[i as int]@ == get_letter_grade(grades[i] as int));
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}
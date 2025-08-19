method AssignmentsToMarkOne(students:int, tutors: int) returns (r:int)
  requires students > 0 && tutors > 1
  ensures r < students
{
  r := students - 1;
}
.task {
  background: #fff;
  color: #333;
  padding: 25px;
  box-sizing: border-box;
  font-family: Comfortaa, sans-serif !important;
  position: relative;
}
.task code, .task_code {
  display: inline-block;
  padding: 0;
  border-radius: 2px;
  margin: 0;
  position: relative;
  top: 6px;
  background: bisque;
  border: 1px solid #f9d2a4;
  padding: 3px;
  line-height: 1em;
}
.task_code {
  top: -1px;
}
.task_header {
  color: #333 !important;
  margin-top: 0;
  font-size: 30px !important;
}
.task_inner {
  box-shadow: 0 2px 11px -3px rgba(0,0,0,.6);
  padding: 20px;
  border-radius: 3px;
}
.task_devil {
  float: right;
  margin-left: 15px;
  shape-outside: circle(150px);
}
.task_devil img {
  max-width: 150px;
}
.task_part-header { 
  font-size: 20px !important;
  font-weight: 800;
  color: #333;
  padding: 20px 0 10px;
}
.task_part-header:first-of-type {
  padding-top: 0;
}
.task_list {
  padding: 0;
  margin: 10px 0;
  padding-left: 30px;
}
.task_list ul {
  padding: 0;
  margin: 0;
}
.font-effect-canvas-print { color: black; }

Devil's Sequence

Problem

    Robodevil likes to do some mathematics between rehearsals of his orchestra. Today he invented devilish sequence No. 1729:

x0 = 0,
x1 = 1,
xn = (xn - 1 + xn - 2) / 2.

    For example, x10 = 0.666015625. Robodevil became interested at once how many `sixes` there were at the beginning of an arbitrary xn. In 6 nanoseconds, he had a formula. Can you do the same?
    Input
    You are given an integer n; `2 ≤ n ≤ 100000`.
    Output
    Output the number of sixes at the beginning of xn in decimal notation.
    Example

Input
Output

10
3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
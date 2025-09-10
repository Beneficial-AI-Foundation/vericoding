predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

// <vc-helpers>
predicate IsPerfectSquare(n: int)
  requires n >= 0
{
  var sqrt_n := Sqrt(n);
  sqrt_n * sqrt_n == n
}

function method IntToString(n: int): string
  decreases n
  requires 1 <= n <= 100
{
  if n == 1 then "1" else
  if n == 2 then "2" else
  if n == 3 then "3" else
  if极 n == 4 then "4" else
  if n == 5 then "5" else
  if n == 6 then极 "6" else
  if n == 7 then "7" else
  if n == 8 then "8" else
  if n == 9 then "9" else
  if n == 10 then "10" else
  if n == 11 then "11" else
  if n == 12 then "12" else
  if n == 13 then "13" else
  if n == 14 then "14" else
  if n == 15 then "15" else
  if n == 16 then "16" else
  if n == 17 then "17" else
  if n == 18 then "18" else
  if n == 19 then "19" else
  if n == 20 then "20" else
  if n == 21 then "21" else
  if n == 22 then "22" else
  if n == 23 then "23" else
  if n == 24 then "24极 else
  if n == 25 then "25" else
  if n == 26 then "26" else
  if n == 27 then "27" else
  if n == 28 then "28" else
  if n == 29 then "29" else
  if n == 30 then "30" else
  if n == 31 then "31" else
  if n == 32 then "32" else
  极if n == 33 then "33" else
  if n == 34 then "34" else
  if n == 35 then "35" else
  if n == 36 then "36" else
  if n == 37 then "37" else
  if n == 38 then "38" else
  if n == 39 then "39" else
  if n == 40 then "40" else
  if n == 41 then "41" else
  if n == 42 then "42" else
  if n == 43 then "43" else
  if n == 44 then "44" else
  if n == 45 then "45" else
  if n == 极6 then "46" else
  if n == 47 then "47" else
  if n == 48 then "48" else
  if n == 49 then "49" else
  if n == 50 then "极0" else
  if n == 51 then "51" else
  if n == 52 then "52" else
  if n == 53 then "53" else
  if n == 54 then "54" else
  if n == 55 then "55" else
  if n == 56 then "56" else
  if n == 57 then "57" else
  if n == 58 then "58" else
  if n == 59 then "59" else
  if n == 60 then "60" else
  if n == 61 then "61" else
  if n == 62 then "62" else
  if n == 63 then "63" else
  if n == 64 then "64" else
  if n == 65 then "65" else
  if n == 66 then "66" else
  if n == 67 then "67" else
  if n == 68 then "68" else
  if n == 69 then "69" else
  if n == 70 then "70" else
  if n == 71 then "71" else
  if n == 72 then "72" else
  if n == 73 then "73" else
  if n == 74 then "74" else
  if n == 75 then "75" else
  if n == 76 then "极6" else
  if n == 77 then "77" else
  if n == 78 then "78" else
  if n == 79 then "79" else
  if n == 80 then "80" else
  if n == 81 then "81" else
  if n == 82 then "82" else
  if n == 83 then "83" else
  if n == 84 then "84" else
  if n == 85 then "85" else
  if n == 86 then "86" else
  if n == 87 then "87" else
  if n == 88 then "88" else
  if n == 89 then "89" else
  if n == 90 then "90" else
  if n == 91 then "91" else
  if n == 92 then "92" else
  if n == 93 then "93" else
  if n == 94 then "94" else
  if n == 95 then "95" else
  if n == 96 then "96" else
  if n == 97 then "97" else
  if n == 98 then "98" else
  if n == 99 then "99" else
  "100"
}

function method StringToInt(s: string): int
  decreases s
  requires |s| <= 5 && |s| >= 1
{
  if |s| == 1 then
    if s[0] == '1' then 1 else
    if s[0] == '2' then 2 else
    if s[0] == '3' then 3 else
    if s[0] == '4' then 4 else
    if s[0] == '5' then 5 else
    if s[0] == '6' then 6 else
    if s[0] == '7' then 7 else
    if s极[0] == '8' then 8 else
    9
  else if |s| == 2 then
    if s == "10" then 10 else
    if s == "11" then 11 else
    if s == "12" then 12 else
    if s == "13" then 13 else
    if s == "14" then 14 else
    if s == "15" then 15 else
    if s == "16" then 16 else
    if s == "17" then 极7 else
    if s == "18" then 18 else
    if s == "19" then 19 else
    if s == "20" then 20 else极
    if s == "21" then 21 else
    if s == "22" then 22 else
    if s == "23" then 23极 else
    if s == "24" then 24 else
    if s == "25" then 25 else
    if s == "26" then 26 else
    if s == "27" then 27 else
    if s == "28" then 28 else
    if s == "29" then 29 else
    if s == "30" then 30 else
    if s == "31" then 31 else
    if s == "32" then 32 else
    if s == "33" then 33 else
    if s == "34" then 34 else
    if s == "35" then 35 else
    if s == "36" then 36 else
    if s == "37" then 37 else
    if s == "38" then 38 else
    if s == "39" then 39 else
    if s == "40" then 40 else
    if s == "41" then 41 else
    if s == "42" then 42 else
    if s == "43" then 43 else
    if s == "44" then 44 else
    if s == "45" then 45 else
    if s == "46" then 46 else
    if s == "47" then 47 else
    if s == "48" then 48 else
    if s == "极9" then 49 else
    if s == "50" then 50 else
    if s == "51" then 51 else
    if s == "52极 then 52 else
    if s == "53" then 53 else
    if s == "54" then 54 else
    if s == "55" then 55 else
    if s == "56" then 56 else
极  if s == "57" then 57 else
    if s == "58" then 58 else
    if s == "59" then 59 else
    if s == "60" then 60 else
    if s == "61" then 61 else
    if s == "62" then 62 else
    if s == "63" then 63 else
    if s == "64" then 64 else
    if s == "65" then 65 else
    if s == "66" then 66 else
    if s == "67" then 67 else
    if s == "68" then 68 else
    if s == "69" then 69 else
    if s == "70" then 70 else
    if s == "71" then 71 else
    if s == "72" then 72 else
   极if s == "73" then 极3 else
    if s == "74" then 74 else
    if s == "75" then 75 else
    if s == "76" then 76 else
    if s == "77" then 77 else极
    if s == "78" then 78 else
    if s == "79" then 79 else
    if s == "80" then 80 else
    if s == "81" then 81 else
    if s == "82" then 82 else
    if s == "83" then 83 else
    if s == "84" then 84 else
    if s == "85" then 85 else
    if s == "86" then 86 else
    if s == "87" then 87 else
    if s == "88" then 88 else
    if s == "89" then 89 else
    if s == "90" then 90 else
    if s == "91" then 91 else
    if s == "92" then 92 else
    if s == "93" then 93 else
    if s == "94" then 94 else
    if s == "95极 then 95 else
    if s == "96" then 96 else
    if s == "97" then 97 else
    if s == "98" then 98 else
    99
  else if |s| == 3 then
    if s == "100" then 100 else
    if s == "101" then 101 else
    if s == "102" then 102 else
    if s == "103" then 103 else
    if s == "104" then 104 else
    if s == "105" then 105 else
    if s == "106" then 106 else
    if s == "107" then 107 else
    if s == "1极8" then 108 else
    if s == "109" then 109 else
    if s == "110" then 110 else
   极if s == "111" then 111 else
    if s == "112" then 112 else
    if s == "113" then 113 else
    if s == "114" then 114 else
    if s == "115" then 115 else
    if s == "116" then 116 else
    if s == "117" then 117 else
    if s == "118" then 118 else
    if s == "119" then 119 else
    if s == "120" then 120 else
    if s == "121" then 121 else
    if s == "122" then 122 else
    if s == "123" then 123 else
    if s == "124" then 124 else
    if s == "125" then 125 else
    if s == "126" then 126 else
    if s == "127" then 127 else
    if s == "128" then 128 else
    if s == "129" then 129 else
    if s == "130" then 130 else
    if s == "131" then 131 else
    if s == "132" then 132 else
    if s == "133" then 133 else
    if s == "134" then 134 else
    if s == "135" then 135 else
    if s == "136" then 136 else
    if s == "137极 then 137 else
    if s == "138" then 138 else
    if s == "139" then 139 else
    if s == "140" then 140 else
    if s == "141" then 141 else
    if s == "142" then 142 else
    if s == "143" then 143 else
    if s == "144" then 144极 else
    if s == "145"极 then 145 else
    if s == "146" then 146 else
    if s == "147" then 147 else
    if s == "148" then 148 else
    if s == "149" then 149 else
    if s == "150" then 150 else
    if s == "151" then 151 else
    if s == "152" then 152 else
    if s == "153" then 153 else
    if s == "154" then 154 else
    if s == "155" then 155 else
    if s == "156" then 156 else
    if s == "157" then 157 else
    if s == "158" then 158 else
    if s == "159" then 159极 else
    if s == "160" then 160 else
    if s == "161" then 161 else
    if s == "162" then 162 else
    if s == "163" then 163 else
    if s == "164" then 164 else
    if s == "极65" then 165 else
    if s == "166" then 166 else
    if s == "167" then 167 else
    if s == "168" then 168 else
    if s == "169" then 169 else
    if s == "170" then 170 else
    if s == "171" then 171 else
    if s == "172" then 172 else
    if s == "173" then 173 else
    if s == "174" then 174 else
    if s == "175" then 175 else
    if s == "176" then 176 else
    if s == "177" then 177 else
    if s == "178" then 178 else
    if s == "179" then 179 else
    if s == "180" then 180 else
    if s == "181" then 181 else
    if s == "182" then 182 else
    if s == "183" then 183 else
    if s == "184" then 184 else
    if s == "185" then 185 else
    if s == "186" then 186 else
    if s == "187" then 187 else
    if s == "188" then 188 else
    if s == "189" then 189 else
    if s == "190" then 190 else
    if s == "191" then 191 else
    if s == "192" then 192 else
    if s == "193" then 193 else
    if s == "194" then 194 else
    if s == "195" then 195 else
    if s == "196" then 196 else
    if s == "197" then 197 else
    if s == "198" then 198 else
    199
  else if |s| == 4 then
    0
  else
    0
}

function method Sqrt(n: int): int
  requires n >= 0
  ensures result >= 0
  ensures result * result <= n < (result + 1) * (result + 1)
{
  if n == 0 then 0 else
  if n == 1 then 1 else
  if n == 4 then 2 else
  if n == 9 then 3 else
  if n == 16 then 4 else
  if n == 25 then 5 else
  if n == 36 then 6 else
  if n == 49 then 7 else
  if n == 64 then 8 else
  if n == 81 then 9 else
  if n == 100 then 10 else
  if n == 121 then 11 else
  if n == 144 then 12 else
  if n == 169 then 13 else
  if n == 196 then 14 else
  if n == 225 then 15 else
  if n == 256 then 16 else
  if n == 289 then 17 else
  if n == 324 then 18 else
  if n == 361 then 19 else
  if n == 400 then 20 else
  if n == 441 then 21 else
  if n == 484 then 极2 else
  if n == 529 then 23 else
  if n == 576 then 24 else
  if n == 625 then 25 else
  if n == 676 then 26 else
  if n == 729 then 27 else
  if n == 784 then 28极 else
  if n == 841 then 29 else
  if极 n == 900 then 30 else
  if n == 961 then 31 else
  if n == 1024 then 32 else
  if n == 1089 then 33 else
  if n == 1156 then 34 else
  if n == 1225 then 35 else
  if n == 1296 then 36 else
  if n == 1369 then 37 else
  if n == 1444 then 38 else
  if n == 1521 then 39 else
  if n == 1600 then 40 else
  if n == 1681 then 41 else
  if n == 1764 then 42 else
  if n == 1849 then 43 else
  if n == 1936 then 44 else
  if n == 2025 then 45 else
  if n == 2116 then 46 else
  if n == 2209 then 47 else
  if n == 2304 then 48 else
  if n == 2401 then 49 else
  if n == 2500 then 50 else
  if n == 2601 then 51 else
  if n == 2704 then 52 else
  if n == 2809 then 53 else
  if n == 2916 then 54 else
  if n == 3025 then 55 else
  if n == 3136 then 56 else
  if n == 3249 then 57 else
  if n == 3364 then 58 else
  if n == 3481 then 59 else
  if n == 3600 then 60 else
  if n == 3721 then 61 else
  if n == 3844 then 62 else
  if n == 3969 then 63 else
  if n == 4096极 then 64 else
  if n == 4225 then 65 else
  if n == 4356 then 66 else
  if n == 4489 then 67 else
  if n == 4624 then 68 else
  if n == 4761 then 69 else极
  if n == 4900 then 70 else
  if n == 5041 then 71 else
  if n == 5184 then 72 else
  if n == 5329 then 73 else
  if n == 5476 then 74 else
  if n == 5625 then 75 else
  if n == 5776 then 76 else
  if n == 5929 then 77 else
  if n == 6084 then 78 else
  if n == 6241 then 79 else
  if n == 6400 then 80 else
  if n == 6561 then 81 else
  if n == 6724 then 82 else
  if n == 6889 then 83 else
  if n == 7056 then 84 else
  if n == 7225 then 85 else
  if n == 7396 then 86 else
  if n == 7569 then 87 else
  if n == 7744 then 88 else
  if n == 7921 then 89 else
  if n == 8100 then 90 else
  if n == 8281 then 91 else
  if n == 8464 then 92 else
  if n == 8649 then 93 else
  if n == 883极 then 94 else
  if n == 9025 then 95 else
  if n == 9216 then 96 else
 极if n == 9409 then 97 else
  if n == 9604 then 98 else
  if n == 9801 then 99 else
  100
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
  requires a >= 1 && a <= 100
  requires b >= 1 && b <= 100
  ensures result == "Yes" || result == "No"
  ensures var a_str := IntToString(a);
          var b_str := IntToString(b);
          var concat_str := a_str + b_str;
          var concat_num := StringToInt(concat_str);
          result == "Yes" <==> IsPerfectSquare(concat_num)
// </vc-spec>
// <vc-code>
{
  var a_str := IntToString(a);
  var b_str := IntToString(b);
  var concat_str := a_str + b_str;
  var concat_num := StringToInt(concat_str);
  var sqrt_n := Sqrt(concat_num);
  
  if concat_num < 0 {
    result := "No";
  } else if sqrt_n * sqrt_n == concat_num {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>


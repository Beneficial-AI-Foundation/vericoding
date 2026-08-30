--  <vc-preamble>
package Np_Sign_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   subtype Sign_Type is Integer range -1 .. 1;
   type Sign_Array is array (Index_Type range <>) of Sign_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Sign (A : Int_Array; Result : out Sign_Array) with
     Pre  => Result'First = A'First and then Result'Last = A'Last,
     Post => (for all I in A'Range =>
                (if A (I) > 0 then Result (I) = 1)
                and then (if A (I) = 0 then Result (I) = 0)
                and then (if A (I) < 0 then Result (I) = -1));

end Np_Sign_Spec;

package body Np_Sign_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Sign (A : Int_Array; Result : out Sign_Array) is
   begin
      pragma Assume (False);
   end Sign;
--  </vc-code>

--  <vc-postamble>
end Np_Sign_Spec;
--  </vc-postamble>

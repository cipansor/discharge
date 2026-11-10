package body Example with SPARK_Mode is

   --  Bug 1: the branches are swapped, so the guarded add is the one that can
   --  overflow.
   function Sat_Add (A, B : Word) return Word is
   begin
      if A > Word'Last - B then
         return A + B;
      else
         return Word'Last;
      end if;
   end Sat_Add;

   --  Bug 2: the body adds 2, so the invariant is not preserved.
   function Sum_To (N : Word) return Word is
      S : Word := 0;
      I : Word := 0;
   begin
      while I < N loop
         pragma Loop_Invariant (I <= N and then S = I);
         pragma Loop_Variant (Increases => I);
         S := S + 2;
         I := I + 1;
      end loop;
      return S;
   end Sum_To;

end Example;

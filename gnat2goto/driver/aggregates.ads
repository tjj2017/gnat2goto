with Types;             use Types;
with Atree;             use Atree;
with Sinfo;             use Sinfo;
with Sem_Eval;          use Sem_Eval;
with Ireps;             use Ireps;
package Aggregates is
   procedure Array_Dynamic_Named_Assoc (Block      : Irep;
                                        Low_Bound  : Irep;
                                        High_Bound : Irep;
                                        N          : Node_Id;
                                        Target     : Irep;
                                        Comp_Type  : Irep)
     with Pre => Nkind (N) = N_Aggregate;

   procedure Array_Dynamic_Positional (Block      : Irep;
                                       Low_Bound  : Irep;
                                       High_Bound : Irep;
                                       N          : Node_Id;
                                       Target     : Irep;
                                       Comp_Type  : Irep)
     with Pre => Nkind (N) = N_Aggregate;

   procedure Array_Static_Named_Assoc (Block      : Irep;
                                       Low_Bound  : Int;
                                       High_Bound : Int;
                                       N          : Node_Id;
                                       Target     : Irep;
                                       Comp_Type  : Irep)
     with Pre => Nkind (N) = N_Aggregate and then
                 Is_OK_Static_Range (Aggregate_Bounds (N));

   procedure Array_Static_Positional (Block      : Irep;
                                      Low_Bound  : Int;
                                      High_Bound : Int;
                                      N          : Node_Id;
                                      Target     : Irep;
                                      Comp_Type  : Irep)
     with Pre => Nkind (N) = N_Aggregate and then
                 Is_OK_Static_Range (Aggregate_Bounds (N));

   procedure Update_Array_From_Aggregate
           (Block                : Irep;
            Agg                  : Node_Id;
            N_Dimensions         : Pos;
            Zero_Based_Low       : Nat;
            Zero_Based_High      : Nat;
            Array_Irep           : Irep;
            Zero_Based_Low_Irep  : Irep;
            Zero_Based_High_Irep : Irep)
     with Pre => Nkind (Agg) = N_Aggregate and
                 Kind (Get_Type (Array_Irep)) = I_Array_Type;

end Aggregates;

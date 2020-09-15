with Types;             use Types;
with Atree;             use Atree;
with Sinfo;             use Sinfo;
with Einfo;             use Einfo;
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

   procedure Initialse_Array_From_Aggregate
           (Block       : Irep;
            Array_Type  : Entity_Id;
            Agg         : Node_Id;
            Array_Irep  : Irep)
     with Pre => Nkind (Agg) = N_Aggregate and Is_Array_Type (Array_Type);

end Aggregates;

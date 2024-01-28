Set Implicit Arguments.

Inductive Expresion :=.

Inductive ColumnName :=.

Inductive DerivedColumn :=
  | expresion : Expresion -> DerivedColumn
  | expresionAs : Expresion -> ColumnName -> DerivedColumn.

Inductive QualifieAsterisk :=.

Inductive SelectSublist :=
  | singleColumn : DerivedColumn -> SelectSublist
  | singleAsterisk : QualifieAsterisk -> SelectSublist.

Inductive SelectList :=
  | asterisk : SelectList
  | sublist : SelectSublist -> SelectList.

Inductive Select := 
  | select : SelectList -> TableExpresion -> Select
  | selectDistinct : SelectList -> TableExpresion -> Select 
  | selectAll : SelectList -> TableExpresion -> Select.
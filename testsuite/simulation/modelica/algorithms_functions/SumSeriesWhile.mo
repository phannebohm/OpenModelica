// name:     SumSeriesWhile
// keywords: while statement
// status:   correct
//
// Drmodelica: 9.1 while-loop (p.290)
//
model SumSeries
  parameter Real eps = 1.E-6;
  Integer i;
  Real sum;
  Real delta;
algorithm
  sum := 0;
  i := 1;
  delta := exp(-0.01 * i);
  while noEvent(delta >= eps) loop
    sum := sum + delta;
    i := i + 1;
    delta := exp(-0.01 * i);
  end while;
  annotation(__OpenModelica_commandLineOptions="-d=-newInst");
end SumSeries;

// class SumSeries
// parameter Real eps = 1e-06;
// Integer i;
// Real sum;
// Real delta;
// algorithm
//   i := 1;
//   delta := exp(-0.01 * Real(i));
//   while delta >= eps loop
//     sum := sum + delta;
//     i := 1 + i;
//     delta := exp(-0.01 * Real(i));
//   end while;
// end SumSeries;

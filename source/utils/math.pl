%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Author: Jose Santos <jcas81@gmail.com>
% Date: 2009-02-17
%
%     This file contains misc. math utility predicates
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(math,
            [
              % the following 4 predicates allow the calculation of a weighted running variance
              initStats/1,
              updateStats/3,
              updateStats/4,
              valueStats/3,

              sqr/2
            ]
         ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% initStats(-stats(NumValues, MeanSoFar, SumWeightsSoFar, VarianceSoFar))
%
%  Returns:
%    a stats term: stats(MeanSoFar, SumWeightsSoFar, VarianceSoFar)
%    that allows the running computation of a mean and, more interestingly, a standard deviation
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

initStats(stats(0, 0, 0, 0)).

%sqr(+X, -Y): Y is unified with X squared
sqr(X, Y):-Y is X*X.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% updateStats(+Value, +Weight, +CurStats, -NextStats)
%
% Given:
%   Value: an arbitrary real number
%   Weight: the weight of this value (a positive real number)
%   CurStats: the current stats term (see initStats/1)
%
% Returns:
%   NextStats: the next stats after considering Value with weight Weight
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

updateStats(Value, Weight, stats(0, 0, 0, 0), stats(1, Value, Weight, 0)):-!.
updateStats(Value, Weight, stats(NumValues, MeanSoFar, SumWeightsSoFar, VarianceSoFar),
            stats(NumValues1, NewMean, NewSumWeights, NewVariance)):-
  NewSumWeights is SumWeightsSoFar+Weight,
  Dif is Value-MeanSoFar,
  sqr(Dif, Dif2),
  NewVariance is VarianceSoFar + SumWeightsSoFar*Weight*Dif2/NewSumWeights,
  NewMean is MeanSoFar + Dif*Weight/NewSumWeights,
  NumValues1 is NumValues+1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% updateStats(+Value, +CurStats, -NextStats)
%
% Given:
%   Value: an arbitrary real number
%   CurStats: the current stats term (see initStats/1)
%
% Returns:
%   NextStats: the next stats after considering Value with weight Weight
%
% Notes:
%   We assume all values have equal weight (=1). Do not mix calling updateStats/3 and updateStats/4 for
%   the same stats term. If you are going to use updateStats/4 then instead of using updateStats/3
%   with implicit weight=1, make the weight explicit
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

updateStats(Value, CurStats, NextStats):-
  updateStats(Value, 1, CurStats, NextStats).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% valueStats(+CurStats, -Mean, -StdDev)
%
% Given:
%   CurStats: the current stats term
%
% Returns:
%   Mean: the mean from the current stats term
%   StdDev: the standard deviation implicit in the stats term
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

valueStats(stats(NumValues, Mean, SumWeightsSoFar, VarianceSoFar), Mean, StdDev):-
  Variance is VarianceSoFar*NumValues/((NumValues-1)*SumWeightsSoFar),
  (Variance>0 -> StdDev is sqrt(Variance) ; StdDev=0). % to protect from errors ..
  % notice that in an earlier Yap6 GIT version nan=:=0

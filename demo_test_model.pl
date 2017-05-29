:- use_module('source/gilps').

%:- show_settings.

:- set(verbose, 3).

% note these theories are being evaluated against a test set (not the examples used to build the model)
proteins:-
  read_problem('datasets/proteins/proteins'),
  evaluate_theory('models/theory_proteins.pl', 'datasets/proteins/examples_test').

pyrimidines:-
  read_problem('datasets/pyrimidines/pyrimidines'),
  evaluate_theory('models/theory_pyrimidines.pl', 'datasets/pyrimidines/extra_examples').
  
:-proteins.
%:-pyrimidines.

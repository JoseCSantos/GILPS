:- use_module('source/gilps').

%:- show_settings.

:- set(verbose, 1).

% reads problem definition and saves learned theory in a file (this is optional)
animals:-
  read_problem('datasets/animals'),
  set(output_theory_file, 'models/theory_animals.pl').
  
trains:-
  read_problem('datasets/trains'),
  set(output_theory_file, 'models/theory_trains.pl').

marriage:-
  read_problem('datasets/marriage'),
  set(output_theory_file, 'models/theory_marriage.pl').

% takes very long time with default settings
mutagenesis:-
  read_problem('datasets/mutagenesis/mutagenesis'),
  set(output_theory_file, 'models/theory_mutagenesis.pl').
  
agatha:-
  read_problem('datasets/agatha'),
  set(output_theory_file, 'models/theory_agatha.pl').
  
:- animals.
%:-trains.
%:-marriage.
%:-agatha.
:- build_theory.

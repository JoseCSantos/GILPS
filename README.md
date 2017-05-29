# GILPS

## What is GILPS

GILPS is the general Inductive Logic Programming System which implements the main contributions
of my PhD work at Imperial College's Computer Science department from 2007 to 2010.

During the research phase of my dissertation many ideas sprang up to test different aspects
of ILP systems. It soon became evident that we would need to develop a generic and modular
ILP system rather than a set of distinct systems each with its own identity but having many
similarities as well, e.g. hypothesis coverage computation, final theory construction, background
knowledge and example handling, and so on.

The main guiding principle in GILPS development has been to ease the addition of new ILP
engines in the framework. The features that are specific to a given ILP engine (e.g. TopLog,
ProGolem) are isolated in a Prolog module with delimited interfaces to the rest of the GILPS
framework. The functionality an existing (or new) ILP engine exports to the GILPS framework
is only how, in this engine, an hypothesis is generated from an example. The GILPS framework
does the rest.

The ideas and algorithms specific to the ILP engines TopLog and ProGolem and the subsumption
engine Subsumer were described in Chapters 3, 4 and 5 of [my thesis](./PhD_Thesis_Jose_Santos.pdf), respectively. 

For further details on GILPS, please see [Chapter 6](./PhD_Thesis_Jose_Santos.pdf) where GILPS is described in more detail.

## How to run

You'll need [YAP Prolog](https://www.dcc.fc.up.pt/~vsc/Yap/downloads.html). Then, in the command line, execute the demo train and test files provided. E.g.

For building models on datasets training data:
yap -l demo_train_model.pl

For testing models on test data:
yap -l demo_test_model.pl

These demos use the default GILPS settings on a few datasets. There are many settings and many datasets to try. Feel free to explore!

/*
 * main.cc
 *
 *  Created on: Jul 29, 2013
 *      Author: yakir
 */

#include "ClsItpSeqMc.h"
#include <iostream>

int main(int argc, char* argv[])
{
    if (argc <= 1)
    {
        std::cout << "No AIG is given in command line\n";
        exit(-1);
    }

    string strFileName = argv[1];

    ClsItpSeqMc cism(strFileName);
    cism.prove();
}



TEST = ../rtest -v

TESTFILES = \
cmakeFMU.mos \
DualMassOscillator_cs.mos \
DualMassOscillator_me.mos \
DualMassOscillator.mos \
enumeration.mos \
enumeration2.mos \
enumeration3.mos \
experimentAnnotation.mos \
fmi_interpolate_cs.mos \
fmiBlackBox.mos \
fmiProtected.mos \
initialization_omc.mos \
initialization.mos \
initialization2_omc.mos \
initialization2.mos \
Issue_FMU_update_vars.mos \
Modelica.Mechanics.MultiBody.Examples.Elementary.Pendulum.mos \
outputState_omc.mos \
outputState.mos \
recompileFMU.mos \
reset_omc.mos \
reset.mos \
setStartTime.mos \
testDirectionalDerivatives.mos \
testLoopsOverFMUs.mos \
testSynchronousFMU_01.mos \
testSynchronousFMU_02.mos \
whenTest.mos \

FAILINGTESTFILES = \
resetWithLoops.mos \
test03.mos \

# Dependency files that are not .mo .mos or Makefile
# Add them here or they will be cleaned.
DEPENDENCIES = \
*.mo \
*.mos \
Makefile \

CLEAN = `ls | grep -w -v -f deps.tmp`

.PHONY : test clean getdeps

test:
	@echo
	@echo Running tests...
	@echo
	@echo OPENMODELICAHOME=" $(OPENMODELICAHOME) "
	@$(TEST) $(TESTFILES)

baseline:
	@echo
	@echo Updating baselines...
	@$(TEST) -b $(TESTFILES)

# Cleans all files that are not listed as dependencies
clean :
	@echo $(DEPENDENCIES) | sed 's/ /\\|/g' > deps.tmp
	@rm -rf $(CLEAN)

# Run this if you want to list out the files (dependencies).
# do it after cleaning and updating the folder
# then you can get a list of file names (which must be dependencies
# since you got them from repository + your own new files)
# then add them to the DEPENDENCIES. You can find the
# list in deps.txt
getdeps:
	@echo $(DEPENDENCIES) | sed 's/ /\\|/g' > deps.tmp
	@echo $(CLEAN) | sed -r 's/deps.txt|deps.tmp//g' | sed 's/ / \\\n/g' > deps.txt
	@echo Dependency list saved in deps.txt.
	@echo Copy the list from deps.txt and add it to the Makefile @DEPENDENCIES

failingtest :
	@echo
	@echo Running failing tests...
	@echo
	@$(TEST) $(FAILINGTESTFILES)

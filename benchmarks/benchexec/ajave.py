# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec
#
# SPDX-FileCopyrightText: 2026 Joss Sheridan-Sheridan
# SPDX-License-Identifier: Apache-2.0

"""
BenchExec tool-info module for ajave, an SV-COMP Java bytecode verifier.

ajave compiles Java source (or loads pre-compiled .class files), lifts them
to an internal IR, runs a portfolio of engines (concrete BMC, SMT BMC,
interval abstract interpretation), and certifies every FALSE by replaying
the witness on a real JVM before reporting.

Usage in a BenchExec XML configuration::

    <benchmark tool="ajave" ...>
      <tasks>
        <include>../sv-benchmarks/java/jbmc-regression/**/*.yml</include>
        <propertyfile>../sv-benchmarks/java/properties/assert.prp</propertyfile>
      </tasks>
    </benchmark>
"""

import benchexec.tools.template
import benchexec.result as result


class Tool(benchexec.tools.template.BaseTool2):
    """Tool-info for ajave."""

    REQUIRED_PATHS = ["."]

    def executable(self, tool_locator):
        return tool_locator.find_executable("ajave")

    def name(self):
        return "ajave"

    def project_url(self):
        return "https://github.com/jossmoff/ajave"

    def version(self, executable):
        return self._version_from_tool(executable, arg="--version")

    def cmdline(self, executable, options, task, rlimits):
        cmd = [executable]
        cmd.extend(options)

        # Pass --property based on the property file.
        prop = task.property_file or ""
        if "no-runtime-exception" in prop:
            cmd.append("--property")
            cmd.append("no-runtime-exception")

        # Pass --witness if BenchExec provides a log file path.
        if hasattr(task, "log_file") and task.log_file:
            import os
            witness_path = os.path.splitext(task.log_file)[0] + ".witness.yml"
            cmd.append("--witness")
            cmd.append(witness_path)

        # BenchExec passes each entry of the task YAML's input_files as a
        # separate path.  ajave accepts them as positional arguments.
        cmd.extend(task.input_files_or_identifier)

        return cmd

    def determine_result(self, run):
        """Parse the verdict from roast's stdout.

        ajave prints exactly one line to stdout: TRUE, FALSE, or UNKNOWN.
        Everything else goes to stderr and is not relevant for the verdict.
        """
        # Detect property from the command line.
        is_nre = "--property" in run.cmdline and "no-runtime-exception" in run.cmdline

        for line in run.output:
            stripped = line.strip()
            if stripped == "TRUE":
                return result.RESULT_TRUE_PROP
            if stripped == "FALSE":
                if is_nre:
                    return result.RESULT_FALSE_DEREF
                return result.RESULT_FALSE_REACH
            if stripped == "UNKNOWN":
                return result.RESULT_UNKNOWN

        # No verdict line found -- treat as error.
        return "ERROR"

#!/usr/bin/env -S isabelle_scala_script -J-Xmx4096M -J-Xms256M

import isabelle._
import java.io.PrintWriter
import java.io.File

def error(str: String) = {
	Console.println(str)
	System.exit(1)
}
def decode_symbols(xml_body: XML.Body): XML.Body = {
	xml_body flatMap {
		case XML.Wrapped_Elem(markup, _, body) => decode_symbols(List(XML.Elem(markup, body)))
		case XML.Elem(markup, body) => List(XML.Elem(markup, decode_symbols(body)))
		case XML.Text(text) => List(XML.Text(Symbol.decode(text)))
	}
}
val thread = Isabelle_Thread.fork(name = "Generate Presentation") {

	val options = Options.init()
	val progress = new Console_Progress(verbose = false)

	val store = Sessions.store(options)

	val dirs = Path.explode(".") :: Nil
	val session = "AOT"

	val selection = Sessions.Selection.session(session)

	val deps = Sessions.load_structure(options, dirs = dirs).selection_deps(Sessions.Selection.session(session))
	val base = deps(session)
	val resources = Resources.empty
	val elements = Presentation.elements1

	progress.interrupt_handler {
		val res = Build.build(options,
			selection = selection,
			dirs = dirs,
			progress = progress,
			verbose = false
		)
		if (!res.ok)
			error("Cannot build session.")

		using(store.open_database_context())(db_context => {
			for (name <- base.session_theories) {
				Console.println("Theory", name)
				val pw = new PrintWriter(new File("pide_markup/" + name + ".xml"))
				for (command <- Build_Job.read_theory(db_context, resources, session, name.theory))
				{
						val snapshot = Document.State.init.snippet(command)
						val files_html =
						for {
							(src_path, xml) <- snapshot.xml_markup_blobs(elements = elements.html)
							if xml.nonEmpty
						}
						yield {
							Console.println("Blob", src_path)
							val pwsub = new PrintWriter(new File("pide_markup/" + src_path.implode + ".xml"))
							for (elem <- xml)
								pwsub.write(elem.toString())
							pwsub.close
						}
						for (elem <- decode_symbols(snapshot.xml_markup(elements = elements.html)))
						{
							pw.write(elem.toString())
						}
				}
				pw.close
			}
		})
	}

	System.exit(0)
}
thread.join()

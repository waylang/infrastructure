require 'rake/clean'

namespace :latex do
  desc 'Compile the Coq metatheory'
  task :compile do
    mkdir_p 'build'
    # Twice to build the table of contents, http://stackoverflow.com/q/3863630/580412
    sh %(pdflatex -output-directory build -jobname way-the-definitive-guide src/book.tex)
    sh %(pdflatex -output-directory build -jobname way-the-definitive-guide src/book.tex)
  end

  desc 'Remove the Latex intermediates'
  task :clean do
    rm_rf 'build'
  end
end

task clean: 'latex:clean'

task default: 'latex:compile'

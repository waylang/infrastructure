require 'rake/clean'

namespace :coq do
  desc 'Compile the Coq metatheory'
  task :compile do
    sh %(coqtop.opt -R src '' -compile Way)
  end

  desc 'Check the Coq metatheory'
  task check: :compile do
    sh %(coqchk.opt -R src '' Way)
  end

  desc 'Remove the Coq intermediates'
  task :clean do
    Dir['src/**/*.{glob,vo}'].each { |file| rm file }
  end
end

task clean: 'coq:clean'

task default: 'coq:check'

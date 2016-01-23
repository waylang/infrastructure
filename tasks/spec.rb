require 'rspec/core/rake_task'

RSpec::Core::RakeTask.new do |rspec_task|
  rspec_task.pattern += ',vendor/infrastructure/spec/project_spec.rb'
end

task default: :spec

desc 'Run all linting and tests'
task :default

# Grab everything in the tasks directory
Dir['vendor/infrastructure/tasks/**/*.rb'].sort.each { |file| require_relative file }
Dir['tasks/**/*.rb'].sort.each { |file| require_relative file }

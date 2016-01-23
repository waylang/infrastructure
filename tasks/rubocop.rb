require 'rubocop/rake_task'

RuboCop::RakeTask.new do |rubocop_task|
  rubocop_task.options = %w(--display-cop-names)
end

task default: :rubocop
